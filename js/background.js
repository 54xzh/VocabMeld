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

let activeRequestCount = 0; // total
let activeTranslationRequestCount = 0;
let activeQueryRequestCount = 0;

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

const apiRequestQueue = []; // translation + other non-query requests
const queryRequestQueue = []; // word query requests (high priority)
let apiQueueProcessing = false;
let apiLastRequestStartAt = 0;
let apiRecentRequestStarts = [];
let apiRequestIdSeq = 1;
const activeApiRequestsById = new Map(); // requestId -> { controller, tabId }
const activeApiRequestIdsByTabId = new Map(); // tabId -> Set(requestId)
const lastNavUrlByTabId = new Map(); // tabId -> normalized url (origin+path+search)
let activeTabId = null;
let focusedWindowId = null;

// Stream request tracking (Port -> Set(requestId))
const streamRequestIdsByPort = new WeakMap();

function safeSendResponse(sendResponse, payload) {
  try {
    sendResponse(payload);
  } catch {
    // ignore (caller tab/frame may be gone)
  }
}

function safePortPostMessage(port, payload) {
  try {
    port.postMessage(payload);
  } catch {
    // ignore (port may be disconnected)
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
  for (const queue of [apiRequestQueue, queryRequestQueue]) {
    for (let i = queue.length - 1; i >= 0; i--) {
      const item = queue[i];
      if (item?.tabId !== tabId) continue;
      queue.splice(i, 1);
      if (item.streamPort && item.streamId) {
        safePortPostMessage(item.streamPort, { type: 'apiStreamError', streamId: item.streamId, error: 'Tab closed' });
      } else if (item.sendResponse) {
        safeSendResponse(item.sendResponse, { success: false, error: 'Tab closed' });
      }
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

function normalizeActiveCountersIfIdle() {
  if (activeRequestCount !== 0) return;
  if (activeTranslationRequestCount !== 0 || activeQueryRequestCount !== 0) {
    activeTranslationRequestCount = 0;
    activeQueryRequestCount = 0;
  }
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

    function pickNextQueueItem(queue, preferredTabId) {
      if (queue.length === 0) return null;
      if (Number.isInteger(preferredTabId)) {
        const idx = queue.findIndex(item => item?.tabId === preferredTabId);
        if (idx >= 0) return queue.splice(idx, 1)[0];
      }
      return queue.shift();
    }

    function scheduleNextSafe() {
      try {
        scheduleNext();
      } catch (e) {
        console.error('[VocabMeld][API] scheduleNext crashed:', e);
        apiQueueProcessing = false;
      }
    }

    // 并行处理请求的辅助函数
    async function processItem(item) {
      const queueType = item?.queueType || 'translation';
      const isQuery = queueType === 'query';
      activeRequestCount++;
      if (isQuery) activeQueryRequestCount++; else activeTranslationRequestCount++;
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
        console.info('[VocabMeld][API] Request start:', endpointLabel, modelLabel, `queue=${queueType}`, `concurrent=${activeRequestCount}`);

        if (item.streamPort && item.streamId) {
          const fullText = await callApiStream(item.endpoint, item.apiKey, item.body, {
            signal: controller.signal,
            onDelta: (delta) => safePortPostMessage(item.streamPort, { type: 'apiStreamDelta', streamId: item.streamId, delta })
          });
          console.info('[VocabMeld][API] Stream success:', endpointLabel, modelLabel, `ms=${Date.now() - startedAt}`);
          safePortPostMessage(item.streamPort, { type: 'apiStreamDone', streamId: item.streamId, text: fullText });
        } else {
          const data = await callApi(item.endpoint, item.apiKey, item.body, { signal: controller.signal });
          console.info('[VocabMeld][API] Request success:', endpointLabel, modelLabel, `ms=${Date.now() - startedAt}`);
          safeSendResponse(item.sendResponse, { success: true, data });
        }
      } catch (error) {
        const endpointLabel = safeEndpointLabel(item.endpoint);
        const modelLabel = item.body?.model ? `model=${item.body.model}` : '';
        console.error('[VocabMeld][API] Request failed:', endpointLabel, modelLabel, `ms=${Date.now() - startedAt}`, error);
        if (item.streamPort && item.streamId) {
          safePortPostMessage(item.streamPort, { type: 'apiStreamError', streamId: item.streamId, error: error?.message || String(error) });
        } else {
          safeSendResponse(item.sendResponse, { success: false, error: error?.message || String(error) });
        }
      } finally {
        untrackActiveApiRequest(requestId);
        activeRequestCount--;
        if (isQuery) activeQueryRequestCount--; else activeTranslationRequestCount--;
        // 当一个请求完成时，尝试启动更多请求
        scheduleNextSafe();
      }
    }

    // 调度下一个请求
    function scheduleNext() {
      normalizeActiveCountersIfIdle();
      const maxConcurrent = apiRateConfig.maxConcurrentRequests || 1;
      const QUERY_RESERVED_SLOTS = 5;
      const wantsQuerySlots = (queryRequestQueue.length > 0 || activeQueryRequestCount > 0);
      // Reserve up to 5 slots for query, but keep at least 1 slot for translation.
      const reservedForQuery = wantsQuerySlots ? Math.min(QUERY_RESERVED_SLOTS, Math.max(0, maxConcurrent - 1)) : 0;
      const maxTranslationConcurrent = wantsQuerySlots ? Math.max(0, maxConcurrent - reservedForQuery) : maxConcurrent;

      while ((queryRequestQueue.length > 0 || apiRequestQueue.length > 0) && activeRequestCount < maxConcurrent) {
        const now = Date.now();
        const delay = computeNextDelayMs(now);

        if (delay > 0) {
          // 需要等待，延迟后再调度
          setTimeout(() => scheduleNextSafe(), delay);
          return;
        }

        // 优先调度查询队列（低延迟）
        let item = pickNextQueueItem(queryRequestQueue, activeTabId);
        if (item) {
          item.queueType = 'query';
          processItem(item);
          continue;
        }

        // 再调度翻译队列，但不占用为查询预留的并发槽位（查询不活跃时不限制）
        if (activeTranslationRequestCount >= maxTranslationConcurrent) return;

        item = pickNextQueueItem(apiRequestQueue, activeTabId);
        if (!item) continue;
        item.queueType = 'translation';

        // 启动请求（不等待完成）
        processItem(item);
      }

      // 如果队列为空且没有活跃请求，结束处理
      if (apiRequestQueue.length === 0 && queryRequestQueue.length === 0 && activeRequestCount === 0) {
        activeTranslationRequestCount = 0;
        activeQueryRequestCount = 0;
        apiQueueProcessing = false;
      }
    }

    // 开始调度
    try {
      scheduleNextSafe();
    } catch (e) {
      console.error('[VocabMeld][API] scheduleNext crashed:', e);
      apiQueueProcessing = false;
    }

  } catch (error) {
    console.error('[VocabMeld][API] Queue processing error:', error);
    apiQueueProcessing = false;
  }
}

function removeQueuedRequestsByIds(ids) {
  if (!ids || ids.size === 0) return;
  for (const queue of [apiRequestQueue, queryRequestQueue]) {
    for (let i = queue.length - 1; i >= 0; i--) {
      const item = queue[i];
      if (ids.has(item?.requestId)) queue.splice(i, 1);
    }
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
      dictionaryType: 'zh-en',
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
  // 手动重置队列（用于恢复偶发卡死）
  if (message.action === 'resetApiQueue') {
    try {
      if (activeRequestCount === 0) {
        activeTranslationRequestCount = 0;
        activeQueryRequestCount = 0;
      }
      apiQueueProcessing = false;
      processApiQueue()
        .then(() => safeSendResponse(sendResponse, { success: true }))
        .catch((err) => safeSendResponse(sendResponse, { success: false, error: err?.message || String(err) }));
    } catch (err) {
      safeSendResponse(sendResponse, { success: false, error: err?.message || String(err) });
    }
    return true;
  }
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

    const isQuery = message.queue === 'query';
    const queue = isQuery ? queryRequestQueue : apiRequestQueue;
    queue.push({
      requestId: apiRequestIdSeq++,
      endpoint: message.endpoint,
      apiKey: message.apiKey,
      body: updatedBody,
      tabId,
      sendResponse,
      queueType: isQuery ? 'query' : 'translation'
    });
    processApiQueue().catch(err => {
      safeSendResponse(sendResponse, { success: false, error: err?.message || String(err) });
    });
    return true;
  }

  // 通用 fetch 代理（避免 content script CORS 限制）
  if (message.action === 'fetchProxy') {
    const url = message.url;
    const init = message.options && typeof message.options === 'object' ? message.options : {};

    (async () => {
      if (!url) {
        safeSendResponse(sendResponse, { success: false, error: 'Missing url' });
        return;
      }

      const controller = new AbortController();
      const timeoutId = setTimeout(() => controller.abort(), 20_000);
      try {
        const resp = await fetch(url, {
          ...init,
          method: (init.method || 'GET'),
          signal: controller.signal
        });
        if (!resp.ok) {
          const text = await resp.text().catch(() => '');
          safeSendResponse(sendResponse, { success: false, error: text || `HTTP ${resp.status}` });
          return;
        }

        const text = await resp.text().catch(() => '');
        try {
          safeSendResponse(sendResponse, { success: true, data: JSON.parse(text) });
        } catch {
          safeSendResponse(sendResponse, { success: true, data: text });
        }
      } catch (err) {
        safeSendResponse(sendResponse, { success: false, error: err?.message || String(err) });
      } finally {
        clearTimeout(timeoutId);
      }
    })();

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
    chrome.storage.local.remove(['vocabmeld_word_cache', 'vocabmeld_word_query_cache', 'vocabmeld_dict_cache'], () => {
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

// 流式 API 请求（Port 形式，支持逐步输出）
chrome.runtime.onConnect.addListener((port) => {
  if (port.name !== 'vocabmeld-api-stream') return;

  port.onMessage.addListener((message) => {
    if (!message || message.action !== 'apiRequestStream') return;

    const body = message.body || {};
    const selectedModel = selectRoundRobinModel(body.model, message.endpoint);
    const updatedBody = { ...body, model: selectedModel, stream: true };
    const tabId = port?.sender?.tab?.id;

    const requestId = apiRequestIdSeq++;
    queryRequestQueue.push({
      requestId,
      endpoint: message.endpoint,
      apiKey: message.apiKey,
      body: updatedBody,
      tabId,
      streamPort: port,
      streamId: message.streamId,
      queueType: 'query'
    });

    const set = streamRequestIdsByPort.get(port) || new Set();
    set.add(requestId);
    streamRequestIdsByPort.set(port, set);

    processApiQueue().catch(err => {
      safePortPostMessage(port, { type: 'apiStreamError', streamId: message.streamId, error: err?.message || String(err) });
    });
  });

  port.onDisconnect.addListener(() => {
    const ids = streamRequestIdsByPort.get(port);
    if (!ids || ids.size === 0) return;
    removeQueuedRequestsByIds(ids);
    for (const requestId of ids) {
      const active = activeApiRequestsById.get(requestId);
      if (active?.controller) {
        try { active.controller.abort(); } catch {}
      }
    }
  });
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

function extractStreamDelta(json) {
  const choice = json?.choices?.[0];
  const delta = choice?.delta;
  if (!delta) return '';
  if (typeof delta === 'string') return delta;
  return String(delta.content ?? delta.text ?? '');
}

async function callApiStream(endpoint, apiKey, body, options = {}) {
  const headers = { 'Content-Type': 'application/json', 'Accept': 'text/event-stream' };
  if (apiKey) headers['Authorization'] = `Bearer ${apiKey}`;

  // 针对 doubao-seed 模型添加 thinking 参数
  let requestBody = body;
  if (body?.model && body.model.includes('doubao-seed')) {
    requestBody = { ...body, thinking: { type: 'disabled' } };
  }

  const TIMEOUT_MS = 60_000;
  const externalSignal = options?.signal;
  const onDelta = typeof options?.onDelta === 'function' ? options.onDelta : null;

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

    const contentType = (response.headers.get('content-type') || '').toLowerCase();
    if (!contentType.includes('text/event-stream') || !response.body) {
      const json = await response.json().catch(() => ({}));
      return String(json?.choices?.[0]?.message?.content || '').trim();
    }

    const reader = response.body.getReader();
    const decoder = new TextDecoder('utf-8');
    let buffer = '';
    let fullText = '';

    while (true) {
      const { value, done } = await reader.read();
      if (done) break;
      buffer += decoder.decode(value, { stream: true });

      // SSE frames split by blank line
      const parts = buffer.split(/\n\n/);
      buffer = parts.pop() || '';

      for (const part of parts) {
        const lines = part.split(/\n/);
        for (const rawLine of lines) {
          const line = rawLine.trim();
          if (!line.startsWith('data:')) continue;
          const data = line.slice(5).trim();
          if (!data) continue;
          if (data === '[DONE]') return fullText;
          let json = null;
          try { json = JSON.parse(data); } catch { json = null; }
          if (!json) continue;
          const delta = extractStreamDelta(json);
          if (!delta) continue;
          fullText += delta;
          if (onDelta) onDelta(delta);
        }
      }
    }

    return fullText;
  } catch (error) {
    if (externalSignal?.aborted) {
      throw new Error('API request aborted');
    }
    if (error?.name === 'AbortError') {
      throw new Error(`API request timeout after ${TIMEOUT_MS}ms`);
    }
    throw error;
  } finally {
    clearTimeout(timeoutId);
    if (externalSignal) {
      externalSignal.removeEventListener('abort', onAbort);
    }
  }
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
