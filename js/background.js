/**
 * VocabMeld 后台脚本
 * 处理扩展级别的事件和消息
 */

// ============ 模型轮询（按逗号分隔） ============
import './logger.js';

const modelRoundRobinState = new Map();

function safeEndpointLabel(endpoint) {
  try {
    const u = new URL(endpoint);
    return `${u.origin}${u.pathname}`;
  } catch {
    return String(endpoint || '');
  }
}

function parseModelList(modelName) {
  if (!modelName || typeof modelName !== 'string') return [];
  return modelName
    .split(',')
    .map(s => s.trim())
    .filter(Boolean);
}

function selectRoundRobinModel(modelName, endpoint = '') {
  const models = parseModelList(modelName);
  if (models.length <= 1) return (models[0] || modelName || '');

  const key = `${endpoint}||${models.join(',')}`;
  const current = modelRoundRobinState.get(key) ?? 0;
  const picked = models[current % models.length];
  modelRoundRobinState.set(key, (current + 1) % models.length);
  return picked;
}

// ============ API 请求限速（RPM + 最小间隔 + 并行数） ============
const DEFAULT_API_RPM_LIMIT = 0; // 0 = unlimited
const DEFAULT_API_REQUEST_INTERVAL_MS = 0; // 0 = unlimited
const DEFAULT_MAX_CONCURRENT_REQUESTS = 1; // 默认单请求（向后兼容）

let apiRateConfig = {
  apiRpmLimit: DEFAULT_API_RPM_LIMIT,
  apiRequestIntervalMs: DEFAULT_API_REQUEST_INTERVAL_MS,
  maxConcurrentRequests: DEFAULT_MAX_CONCURRENT_REQUESTS
};

let activeRequestCount = 0; // 当前正在进行的请求数

let apiRateConfigLoaded = false;
let apiRateConfigLoadingPromise = null;

function clampNumber(value, min, max, fallback) {
  const n = Number(value);
  if (!Number.isFinite(n)) return fallback;
  return Math.min(max, Math.max(min, n));
}

async function loadApiRateConfig() {
  if (apiRateConfigLoaded) return apiRateConfig;
  if (apiRateConfigLoadingPromise) return apiRateConfigLoadingPromise;

  apiRateConfigLoadingPromise = new Promise((resolve) => {
    chrome.storage.sync.get(['apiRpmLimit', 'apiRequestIntervalMs', 'maxConcurrentRequests'], (result) => {
      apiRateConfig = {
        apiRpmLimit: clampNumber(result.apiRpmLimit ?? DEFAULT_API_RPM_LIMIT, 0, 600, DEFAULT_API_RPM_LIMIT),
        apiRequestIntervalMs: clampNumber(result.apiRequestIntervalMs ?? DEFAULT_API_REQUEST_INTERVAL_MS, 0, 60000, DEFAULT_API_REQUEST_INTERVAL_MS),
        maxConcurrentRequests: clampNumber(result.maxConcurrentRequests ?? DEFAULT_MAX_CONCURRENT_REQUESTS, 1, 100, DEFAULT_MAX_CONCURRENT_REQUESTS)
      };
      apiRateConfigLoaded = true;
      resolve(apiRateConfig);
    });
  }).finally(() => {
    apiRateConfigLoadingPromise = null;
  });

  return apiRateConfigLoadingPromise;
}

chrome.storage.onChanged.addListener((changes, areaName) => {
  if (areaName !== 'sync') return;
  if (changes.apiRpmLimit) {
    apiRateConfig.apiRpmLimit = clampNumber(changes.apiRpmLimit.newValue ?? DEFAULT_API_RPM_LIMIT, 0, 600, DEFAULT_API_RPM_LIMIT);
    apiRateConfigLoaded = true;
  }
  if (changes.apiRequestIntervalMs) {
    apiRateConfig.apiRequestIntervalMs = clampNumber(changes.apiRequestIntervalMs.newValue ?? DEFAULT_API_REQUEST_INTERVAL_MS, 0, 60000, DEFAULT_API_REQUEST_INTERVAL_MS);
    apiRateConfigLoaded = true;
  }
  if (changes.maxConcurrentRequests) {
    apiRateConfig.maxConcurrentRequests = clampNumber(changes.maxConcurrentRequests.newValue ?? DEFAULT_MAX_CONCURRENT_REQUESTS, 1, 100, DEFAULT_MAX_CONCURRENT_REQUESTS);
    apiRateConfigLoaded = true;
  }
});

const apiRequestQueue = [];
let apiQueueProcessing = false;
let apiLastRequestStartAt = 0;
let apiRecentRequestStarts = [];
let apiRequestIdSeq = 1;
const activeApiRequestsById = new Map(); // requestId -> { controller, tabId }
const activeApiRequestIdsByTabId = new Map(); // tabId -> Set(requestId)
const lastNavUrlByTabId = new Map(); // tabId -> normalized url (origin+path+search)
let activeTabId = null;
let focusedWindowId = null;

function safeSendResponse(sendResponse, payload) {
  try {
    sendResponse(payload);
  } catch {
    // ignore (caller tab/frame may be gone)
  }
}

function trackActiveApiRequest(tabId, requestId, controller) {
  if (!Number.isInteger(tabId)) return;
  activeApiRequestsById.set(requestId, { controller, tabId });
  const set = activeApiRequestIdsByTabId.get(tabId) || new Set();
  set.add(requestId);
  activeApiRequestIdsByTabId.set(tabId, set);
}

function untrackActiveApiRequest(requestId) {
  const entry = activeApiRequestsById.get(requestId);
  if (!entry) return;
  activeApiRequestsById.delete(requestId);
  const set = activeApiRequestIdsByTabId.get(entry.tabId);
  if (!set) return;
  set.delete(requestId);
  if (set.size === 0) activeApiRequestIdsByTabId.delete(entry.tabId);
}

function cancelRequestsForTab(tabId) {
  // Abort in-flight requests
  const ids = activeApiRequestIdsByTabId.get(tabId);
  if (ids) {
    for (const requestId of Array.from(ids)) {
      const entry = activeApiRequestsById.get(requestId);
      if (entry?.controller) entry.controller.abort();
      untrackActiveApiRequest(requestId);
    }
  }

  // Drop queued requests
  for (let i = apiRequestQueue.length - 1; i >= 0; i--) {
    const item = apiRequestQueue[i];
    if (item?.tabId === tabId) {
      apiRequestQueue.splice(i, 1);
      safeSendResponse(item.sendResponse, { success: false, error: 'Tab closed' });
    }
  }
}

chrome.tabs.onRemoved.addListener((tabId) => {
  cancelRequestsForTab(tabId);
  lastNavUrlByTabId.delete(tabId);
  if (activeTabId === tabId) activeTabId = null;
});

function normalizeNavUrl(url) {
  try {
    const u = new URL(url);
    if (u.protocol !== 'http:' && u.protocol !== 'https:') return null;
    return `${u.origin}${u.pathname}${u.search}`;
  } catch {
    return null;
  }
}

function sleep(ms) {
  return new Promise(resolve => setTimeout(resolve, ms));
}

function refreshActiveTabFromWindow(windowId) {
  if (!Number.isInteger(windowId) || windowId === chrome.windows.WINDOW_ID_NONE) return;
  chrome.tabs.query({ active: true, windowId }, (tabs) => {
    const tab = tabs?.[0];
    if (tab?.id != null) activeTabId = tab.id;
  });
}

chrome.windows.onFocusChanged.addListener((windowId) => {
  focusedWindowId = windowId;
  if (windowId === chrome.windows.WINDOW_ID_NONE) {
    activeTabId = null;
    return;
  }
  refreshActiveTabFromWindow(windowId);
});

chrome.tabs.onActivated.addListener((activeInfo) => {
  activeTabId = activeInfo.tabId;
  focusedWindowId = activeInfo.windowId;
});

function pruneOldRequests(now) {
  const cutoff = now - 60_000;
  apiRecentRequestStarts = apiRecentRequestStarts.filter(t => t >= cutoff);
}

function computeNextDelayMs(now) {
  const rpmLimit = apiRateConfig.apiRpmLimit || 0;
  const minIntervalMs = apiRateConfig.apiRequestIntervalMs || 0;

  let delay = 0;

  if (minIntervalMs > 0 && apiLastRequestStartAt > 0) {
    delay = Math.max(delay, (apiLastRequestStartAt + minIntervalMs) - now);
  }

  if (rpmLimit > 0) {
    pruneOldRequests(now);
    if (apiRecentRequestStarts.length >= rpmLimit) {
      const earliest = apiRecentRequestStarts[0];
      delay = Math.max(delay, (earliest + 60_000) - now);
    }
  }

  return Math.max(0, delay);
}

async function processApiQueue() {
  if (apiQueueProcessing) return;
  apiQueueProcessing = true;

  try {
    await loadApiRateConfig();

    function pickNextQueueItem(preferredTabId) {
      if (apiRequestQueue.length === 0) return null;
      if (Number.isInteger(preferredTabId)) {
        const idx = apiRequestQueue.findIndex(item => item?.tabId === preferredTabId);
        if (idx >= 0) return apiRequestQueue.splice(idx, 1)[0];
      }
      return apiRequestQueue.shift();
    }

    // 并行处理请求的辅助函数
    async function processItem(item) {
      activeRequestCount++;
      const startedAt = Date.now();
      apiLastRequestStartAt = startedAt;
      apiRecentRequestStarts.push(startedAt);
      pruneOldRequests(startedAt);
      const requestId = item.requestId;
      const controller = new AbortController();
      trackActiveApiRequest(item.tabId, requestId, controller);

      try {
        const endpointLabel = safeEndpointLabel(item.endpoint);
        const modelLabel = item.body?.model ? `model=${item.body.model}` : '';
        console.info('[VocabMeld][API] Request start:', endpointLabel, modelLabel, `concurrent=${activeRequestCount}`);

        const data = await callApi(item.endpoint, item.apiKey, item.body, { signal: controller.signal });
        console.info('[VocabMeld][API] Request success:', endpointLabel, modelLabel, `ms=${Date.now() - startedAt}`);
        safeSendResponse(item.sendResponse, { success: true, data });
      } catch (error) {
        const endpointLabel = safeEndpointLabel(item.endpoint);
        const modelLabel = item.body?.model ? `model=${item.body.model}` : '';
        console.error('[VocabMeld][API] Request failed:', endpointLabel, modelLabel, `ms=${Date.now() - startedAt}`, error);
        safeSendResponse(item.sendResponse, { success: false, error: error?.message || String(error) });
      } finally {
        untrackActiveApiRequest(requestId);
        activeRequestCount--;
        // 当一个请求完成时，尝试启动更多请求
        scheduleNext();
      }
    }

    // 调度下一个请求
    async function scheduleNext() {
      const maxConcurrent = apiRateConfig.maxConcurrentRequests || 1;

      while (apiRequestQueue.length > 0 && activeRequestCount < maxConcurrent) {
        const now = Date.now();
        const delay = computeNextDelayMs(now);

        if (delay > 0) {
          // 需要等待，延迟后再调度
          setTimeout(() => scheduleNext(), delay);
          return;
        }

        const item = pickNextQueueItem(activeTabId);
        if (!item) continue;

        // 启动请求（不等待完成）
        processItem(item);
      }

      // 如果队列为空且没有活跃请求，结束处理
      if (apiRequestQueue.length === 0 && activeRequestCount === 0) {
        apiQueueProcessing = false;
      }
    }

    // 开始调度
    scheduleNext();

  } catch (error) {
    console.error('[VocabMeld][API] Queue processing error:', error);
    apiQueueProcessing = false;
  }
}


// 安装/更新时初始化
chrome.runtime.onInstalled.addListener((details) => {
  console.log('[VocabMeld] Extension installed/updated:', details.reason);

  // 设置默认配置
  if (details.reason === 'install') {
    chrome.storage.sync.set({
      apiEndpoint: 'https://api.deepseek.com/chat/completions',
      apiKey: '',
      modelName: 'deepseek-chat',
      apiRpmLimit: DEFAULT_API_RPM_LIMIT,
      apiRequestIntervalMs: DEFAULT_API_REQUEST_INTERVAL_MS,
      maxConcurrentRequests: DEFAULT_MAX_CONCURRENT_REQUESTS,
      nativeLanguage: 'zh-CN',
      targetLanguage: 'en',
      difficultyLevel: 'B1',
      intensity: 'medium',
      autoProcess: true,
      showPhonetic: true,
      translationStyle: 'translation-original',
      // 句子/段落翻译（额外翻译为学习语言）
      sentenceTranslationRate: 0,
      paragraphTranslationRate: 0,
      enabled: true,
      siteMode: 'all',
      excludedSites: [],
      allowedSites: [],
      learnedWords: [],
      memorizeList: [],
      totalWords: 0,
      todayWords: 0,
      lastResetDate: new Date().toISOString().split('T')[0],
      cacheHits: 0,
      cacheMisses: 0
    });
  }

  // 创建右键菜单
  createContextMenus();
});

// 创建右键菜单
function createContextMenus() {
  chrome.contextMenus.removeAll(() => {
    chrome.contextMenus.create({
      id: 'vocabmeld-add-memorize',
      title: '添加到需记忆列表',
      contexts: ['selection']
    });

    chrome.contextMenus.create({
      id: 'vocabmeld-process-page',
      title: '处理当前页面',
      contexts: ['page']
    });
  });
}

// 右键菜单点击处理
chrome.contextMenus.onClicked.addListener((info, tab) => {
  if (info.menuItemId === 'vocabmeld-add-memorize' && info.selectionText) {
    const word = info.selectionText.trim();
    if (word && word.length < 50) {
      chrome.storage.sync.get('memorizeList', (result) => {
        const list = result.memorizeList || [];
        if (!list.some(w => w.word === word)) {
          list.push({ word, addedAt: Date.now() });
          chrome.storage.sync.set({ memorizeList: list }, () => {
            // 通知 content script 处理特定单词
            chrome.tabs.sendMessage(tab.id, {
              action: 'processSpecificWords',
              words: [word]
            }).catch(err => {
              console.log('[VocabMeld] Content script not ready, word will be processed on next page load');
            });
          });
        }
      });
    }
  }

  if (info.menuItemId === 'vocabmeld-process-page') {
    chrome.tabs.sendMessage(tab.id, { action: 'processPage' });
  }
});

// 快捷键处理
chrome.commands.onCommand.addListener((command, tab) => {
  if (command === 'toggle-translation') {
    chrome.tabs.sendMessage(tab.id, { action: 'processPage' });
  }
});

// 消息处理
chrome.runtime.onMessage.addListener((message, sender, sendResponse) => {
  // 语音合成
  if (message.action === 'speak') {
    const text = message.text;
    const lang = message.lang || 'en-US';

    // 获取用户配置的语音设置
    chrome.storage.sync.get(['ttsRate', 'ttsVoice'], (settings) => {
      const rate = settings.ttsRate || 1.0;
      const preferredVoice = settings.ttsVoice || '';

      // 先停止之前的朗读
      chrome.tts.stop();

      const options = {
        lang: lang,
        rate: rate,
        pitch: 1.0
      };

      // 如果用户指定了声音，使用用户的选择
      if (preferredVoice) {
        options.voiceName = preferredVoice;
      }

      chrome.tts.speak(text, options, () => {
        if (chrome.runtime.lastError) {
          console.error('[VocabMeld] TTS Error:', chrome.runtime.lastError.message);
          sendResponse({ success: false, error: chrome.runtime.lastError.message });
        } else {
          sendResponse({ success: true });
        }
      });
    });

    return true;
  }

  // 获取可用的 TTS 声音列表
  if (message.action === 'getVoices') {
    chrome.tts.getVoices((voices) => {
      sendResponse({ voices: voices || [] });
    });
    return true;
  }

  // 测试 API 连接
  if (message.action === 'testApi') {
    testApiConnection(message.endpoint, message.apiKey, message.model)
      .then(result => sendResponse(result))
      .catch(error => sendResponse({ success: false, message: error.message }));
    return true;
  }

  // 发送 API 请求（避免 CORS 问题）
  if (message.action === 'apiRequest') {
    const body = message.body || {};
    const selectedModel = selectRoundRobinModel(body.model, message.endpoint);
    const updatedBody = { ...body, model: selectedModel };
    const tabId = sender?.tab?.id;

    apiRequestQueue.push({
      requestId: apiRequestIdSeq++,
      endpoint: message.endpoint,
      apiKey: message.apiKey,
      body: updatedBody,
      tabId,
      sendResponse
    });
    processApiQueue().catch(err => {
      safeSendResponse(sendResponse, { success: false, error: err?.message || String(err) });
    });
    return true;
  }

  // 获取统计数据
  if (message.action === 'getStats') {
    chrome.storage.sync.get([
      'totalWords', 'todayWords', 'lastResetDate',
      'cacheHits', 'cacheMisses', 'learnedWords', 'memorizeList'
    ], (result) => {
      // 检查是否需要重置今日统计
      const today = new Date().toISOString().split('T')[0];
      if (result.lastResetDate !== today) {
        result.todayWords = 0;
        result.lastResetDate = today;
        chrome.storage.sync.set({ todayWords: 0, lastResetDate: today });
      }

      sendResponse({
        totalWords: result.totalWords || 0,
        todayWords: result.todayWords || 0,
        learnedCount: (result.learnedWords || []).length,
        memorizeCount: (result.memorizeList || []).length,
        cacheHits: result.cacheHits || 0,
        cacheMisses: result.cacheMisses || 0
      });
    });
    return true;
  }

  // 获取缓存统计
  if (message.action === 'getCacheStats') {
    chrome.storage.sync.get('cacheMaxSize', (syncResult) => {
      const maxSize = syncResult.cacheMaxSize || 2000;
      chrome.storage.local.get('vocabmeld_word_cache', (result) => {
        const cache = result.vocabmeld_word_cache || [];
        sendResponse({
          size: cache.length,
          maxSize: maxSize
        });
      });
    });
    return true;
  }

  // 清空缓存
  if (message.action === 'clearCache') {
    chrome.storage.local.remove(['vocabmeld_word_cache', 'vocabmeld_word_query_cache'], () => {
      chrome.storage.sync.set({ cacheHits: 0, cacheMisses: 0 }, () => {
        sendResponse({ success: true });
      });
    });
    return true;
  }

  // 清空已学会词汇
  if (message.action === 'clearLearnedWords') {
    chrome.storage.sync.set({ learnedWords: [] }, () => {
      sendResponse({ success: true });
    });
    return true;
  }

  // 清空需记忆列表
  if (message.action === 'clearMemorizeList') {
    chrome.storage.sync.set({ memorizeList: [] }, () => {
      sendResponse({ success: true });
    });
    return true;
  }
});

// 通用 API 调用（从 background 发起，避免 CORS）
async function callApi(endpoint, apiKey, body, options = {}) {
  const headers = { 'Content-Type': 'application/json' };
  if (apiKey) headers['Authorization'] = `Bearer ${apiKey}`;

  // 针对 doubao-seed 模型添加 thinking 参数
  let requestBody = body;
  if (body?.model && body.model.includes('doubao-seed')) {
    requestBody = { ...body, thinking: { type: 'disabled' } };
  }

  const MAX_RETRIES = 2;
  const TIMEOUT_MS = 60_000;
  const externalSignal = options?.signal;

  function sleepWithAbort(ms) {
    if (!externalSignal) return sleep(ms);
    return new Promise((resolve, reject) => {
      if (externalSignal.aborted) {
        reject(new DOMException('Aborted', 'AbortError'));
        return;
      }
      let t;
      const onAbort = () => {
        clearTimeout(t);
        externalSignal.removeEventListener('abort', onAbort);
        reject(new DOMException('Aborted', 'AbortError'));
      };
      const onDone = () => {
        externalSignal.removeEventListener('abort', onAbort);
        resolve();
      };
      t = setTimeout(onDone, ms);
      externalSignal.addEventListener('abort', onAbort, { once: true });
    });
  }

  for (let attempt = 0; attempt <= MAX_RETRIES; attempt++) {
    if (externalSignal?.aborted) {
      throw new Error('API request aborted (tab closed)');
    }
    const controller = new AbortController();
    const onAbort = () => controller.abort();
    if (externalSignal) {
      externalSignal.addEventListener('abort', onAbort, { once: true });
    }
    const timeoutId = setTimeout(() => controller.abort(), TIMEOUT_MS);

    try {
      const response = await fetch(endpoint, {
        method: 'POST',
        headers,
        body: JSON.stringify(requestBody),
        signal: controller.signal
      });

      if ((response.status === 429 || response.status === 503) && attempt < MAX_RETRIES) {
        const retryAfter = response.headers.get('retry-after');
        let waitMs = 500 * Math.pow(2, attempt);
        const retryAfterSeconds = Number(retryAfter);
        if (Number.isFinite(retryAfterSeconds) && retryAfterSeconds > 0) {
          waitMs = Math.max(waitMs, retryAfterSeconds * 1000);
        } else if (retryAfter) {
          const retryAt = Date.parse(retryAfter);
          if (Number.isFinite(retryAt)) {
            waitMs = Math.max(waitMs, retryAt - Date.now());
          }
        }
        await sleepWithAbort(Math.min(30_000, Math.max(0, waitMs)));
        continue;
      }

      if (!response.ok) {
        const contentType = (response.headers.get('content-type') || '').toLowerCase();
        let message = `API Error: ${response.status}`;
        if (contentType.includes('application/json')) {
          const error = await response.json().catch(() => ({}));
          message = error.error?.message || error.message || message;
        } else {
          const text = await response.text().catch(() => '');
          if (text) message = text.slice(0, 500);
        }
        throw new Error(message);
      }

      return await response.json();
    } catch (error) {
      if (externalSignal?.aborted) {
        throw new Error('API request aborted (tab closed)');
      }
      if (error?.name === 'AbortError') {
        throw new Error(`API request timeout after ${TIMEOUT_MS}ms`);
      }
      if (attempt >= MAX_RETRIES) throw error;
      await sleepWithAbort(Math.min(2_000, 250 * Math.pow(2, attempt)));
    } finally {
      clearTimeout(timeoutId);
      if (externalSignal) {
        externalSignal.removeEventListener('abort', onAbort);
      }
    }
  }

  throw new Error('API request failed after retries');
}

// 测试 API 连接
async function testApiConnection(endpoint, apiKey, model) {
  const endpointLabel = safeEndpointLabel(endpoint);
  try {
    console.info('[VocabMeld][API] Test connection start:', endpointLabel, model ? `model=${model}` : '');
    const headers = { 'Content-Type': 'application/json' };
    if (apiKey) headers['Authorization'] = `Bearer ${apiKey}`;

    // 如填写多个模型，测试时默认取第一个（避免一次测试触发多次请求）
    const selectedModel = parseModelList(model)?.[0] || model;

    const response = await fetch(endpoint, {
      method: 'POST',
      headers,
      body: JSON.stringify({
        model: selectedModel,
        messages: [{ role: 'user', content: 'Say OK' }],
        max_tokens: 10
      })
    });

    if (!response.ok) {
      const error = await response.json().catch(() => ({}));
      throw new Error(error.error?.message || `HTTP ${response.status}`);
    }

    const data = await response.json();
    if (data.choices && data.choices[0]) {
      console.info('[VocabMeld][API] Test connection success:', endpointLabel, selectedModel ? `model=${selectedModel}` : '');
      return { success: true, message: '连接成功！' };
    }

    throw new Error('Invalid response');
  } catch (error) {
    console.error('[VocabMeld][API] Test connection failed:', endpointLabel, error);
    return { success: false, message: error.message };
  }
}

// 扩展图标点击（如果没有 popup）
chrome.action.onClicked.addListener((tab) => {
  // 由于我们有 popup，这个不会被触发
  // 但保留以防万一
});

// 标签页更新时检查是否需要注入脚本
chrome.tabs.onUpdated.addListener((tabId, changeInfo, tab) => {
  // Cancel pending/in-flight API work when a tab navigates or reloads.
  // - status=loading: full page navigation/reload
  // - url changed: SPA-style navigation (ignore hash-only changes via normalization)
  if (changeInfo.status === 'loading') {
    cancelRequestsForTab(tabId);
  } else if (changeInfo.url) {
    const next = normalizeNavUrl(changeInfo.url);
    if (next) {
      const prev = lastNavUrlByTabId.get(tabId);
      if (prev && prev !== next) {
        cancelRequestsForTab(tabId);
      }
      lastNavUrlByTabId.set(tabId, next);
    }
  }

  if (changeInfo.status === 'complete' && tab.url?.startsWith('http')) {
    const base = normalizeNavUrl(tab.url);
    if (base) lastNavUrlByTabId.set(tabId, base);
    // 可以在这里做额外的初始化
  }
});

console.log('[VocabMeld] Background script loaded');
