/**
 * VocabMeld 内容脚本
 * 注入到网页中，处理词汇替换和用户交互
 */

// 由于 content script 不支持 ES modules，我们需要将所有代码整合

(async function() {
  'use strict';

  // ============ 配置常量 ============
  const CEFR_LEVELS = ['A1', 'A2', 'B1', 'B2', 'C1', 'C2'];
  const INTENSITY_CONFIG = {
    low: { maxPerParagraph: 4 },
    medium: { maxPerParagraph: 8 },
    high: { maxPerParagraph: 14 }
  };
  const SKIP_TAGS = ['SCRIPT', 'STYLE', 'NOSCRIPT', 'IFRAME', 'CODE', 'PRE', 'KBD', 'TEXTAREA', 'INPUT', 'SELECT', 'BUTTON'];
  const SKIP_CLASSES = [
    'vocabmeld-translated',
    'vocabmeld-tooltip',
    'vocabmeld-segment-translated',
    'vocabmeld-paragraph-translated',
    'vocabmeld-paragraph-original',
    'hljs',
    'code',
    'syntax'
  ];
  const DEFAULT_CACHE_MAX_SIZE = 2000;
  const DEFAULT_WORD_QUERY_CACHE_MAX_SIZE = 500;
  const WORD_QUERY_CACHE_STORAGE_KEY = 'vocabmeld_word_query_cache';
  const WORD_QUERY_HOVER_DELAY_MS = 200;
  const DICT_CACHE_STORAGE_KEY = 'vocabmeld_dict_cache';
  const DICT_CACHE_MAX_SIZE = 500;
  const DEFAULT_SENTENCE_TRANSLATION_RATE = 0; // 0-100
  const DEFAULT_PARAGRAPH_TRANSLATION_RATE = 0; // 0-100
  const MAX_SENTENCE_TRANSLATIONS_PER_PARAGRAPH = 3;
  const MAX_SENTENCE_CHARS = 280;
  const MIN_SENTENCE_CHARS = 20;
  const MAX_INLINE_TRANSLATION_CHARS = 2000;
  const PROCESSING_ATTR = 'data-vocabmeld-processing';
  const SCANNED_ATTR = 'data-vocabmeld-scanned';
  const VIEWPORT_PREFETCH_MARGIN_PX = 600; // 优先处理视口附近（上下文）内容
  const STOP_WORDS = new Set([
    'the', 'a', 'an', 'is', 'are', 'was', 'were', 'be', 'been', 'being',
    'have', 'has', 'had', 'do', 'does', 'did', 'will', 'would', 'could', 'should',
    'may', 'might', 'must', 'shall', 'can', 'need', 'dare', 'ought', 'used',
    'to', 'of', 'in', 'for', 'on', 'with', 'at', 'by', 'from', 'as', 'into',
    'through', 'during', 'before', 'after', 'above', 'below', 'between', 'under',
    'again', 'further', 'then', 'once', 'here', 'there', 'when', 'where', 'why', 'how',
    'all', 'each', 'few', 'more', 'most', 'other', 'some', 'such', 'no', 'nor', 'not',
    'only', 'own', 'same', 'so', 'than', 'too', 'very', 'just', 'and', 'but', 'if',
    'or', 'because', 'until', 'while', 'this', 'that', 'these', 'those', 'what',
    'which', 'who', 'whom', 'i', 'you', 'he', 'she', 'it', 'we', 'they', 'me',
    'him', 'her', 'us', 'them', 'my', 'your', 'his', 'its', 'our', 'their'
  ]);
  const TEXT_CONTAINER_TAGS = new Set(['P', 'DIV', 'ARTICLE', 'SECTION', 'LI', 'TD', 'TH', 'H1', 'H2', 'H3', 'H4', 'H5', 'H6', 'SPAN', 'BLOCKQUOTE']);
  const INLINE_TRANSLATION_ALLOWED_TAGS = new Set(['P', 'DIV', 'LI', 'ARTICLE', 'SECTION', 'BLOCKQUOTE']);

  // ============ 状态管理 ============
  let config = null;
  let isProcessing = false;
  let processedFingerprints = new Set();
  let wordCache = new Map();
  let wordQueryCache = new Map(); // key -> { data, savedAt }
  let wordQueryInFlight = new Map(); // key -> { promise, cancel, listeners, state }
  let wordQueryCacheSaveTimer = null;
  let wordQueryHoverTimer = null;
  let lastWordQueryHoverKey = '';
  let wordQueryHoverStream = null; // { key, cancel }
  let activeWordQueryStream = null; // { key, cancel }
  let cachedCjkWordsByLangPair = new Map(); // `${sourceLang}:${targetLang}` -> Set(lowerCjkWord)
  let dictCache = new Map(); // cacheKey -> dictData|null
  let persistentDictCache = null; // Map(cacheKey -> dictData|null), LRU
  let dictCacheInitPromise = null;
  let dictPersistTimer = null;
  let tooltipExplainMode = 'ai'; // 'ai' | 'dict'
  let tooltip = null;
  let selectionPopup = null;
  let intersectionObserver = null;
  let pendingContainers = new Set(); // 待处理的可见容器
  let observedContainers = new WeakSet(); // avoid repeated IntersectionObserver.observe calls
  let tooltipHideTimeout = null; // tooltip 延迟隐藏计时器
  let activeTooltipTarget = null;
  let isTabActive = !document.hidden;
  // removed: global retry FAB (deduped)

  // ============ 工具函数 ============
  function isDifficultyCompatible(wordDifficulty, userDifficulty) {
    const wordIdx = CEFR_LEVELS.indexOf(wordDifficulty);
    const userIdx = CEFR_LEVELS.indexOf(userDifficulty);
    return wordIdx >= userIdx;
  }

  function generateFingerprint(text, path = '') {
    const content = text.slice(0, 100).trim();
    let hash = 0;
    const str = content + path;
    for (let i = 0; i < str.length; i++) {
      const char = str.charCodeAt(i);
      hash = ((hash << 5) - hash) + char;
      hash = hash & hash;
    }
    return hash.toString(36);
  }

  function debounce(func, wait) {
    let timeout;
    return (...args) => {
      clearTimeout(timeout);
      timeout = setTimeout(() => func.apply(this, args), wait);
    };
  }

  function detectLanguage(text) {
    const chineseRegex = /[\u4e00-\u9fff]/g;
    const japaneseRegex = /[\u3040-\u309f\u30a0-\u30ff]/g;
    const koreanRegex = /[\uac00-\ud7af]/g;
    const latinRegex = /[a-zA-Z]/g;

    const chineseCount = (text.match(chineseRegex) || []).length;
    const japaneseCount = (text.match(japaneseRegex) || []).length;
    const koreanCount = (text.match(koreanRegex) || []).length;
    const latinCount = (text.match(latinRegex) || []).length;
    const total = chineseCount + japaneseCount + koreanCount + latinCount || 1;

    if (japaneseCount / total > 0.1) return 'ja';
    if (koreanCount / total > 0.1) return 'ko';
    if (chineseCount / total > 0.3) return 'zh'; // 返回通用中文标识
    return 'en';
  }

  function isBilibiliVideoPage() {
    const host = (window.location.hostname || '').toLowerCase();
    if (!/(^|\.)bilibili\.com$/.test(host)) return false;
    return (window.location.pathname || '').startsWith('/video/');
  }

  function isLikelyBilibiliCommentContainer(element) {
    if (!isBilibiliVideoPage() || !element?.tagName) return false;
    let current = element;
    for (let i = 0; current && i < 10; i++) {
      const id = (current.id || '').toLowerCase();
      const cls = (current.className || '').toString().toLowerCase();
      if (id.includes('comment') || cls.includes('comment') || cls.includes('reply')) return true;
      current = current.parentElement;
    }
    return false;
  }

  // 判断检测到的语言是否与用户设置的母语匹配
  function isNativeLanguage(detectedLang, nativeLang) {
    // 中文简繁体视为同一语系
    if (detectedLang === 'zh' && (nativeLang === 'zh-CN' || nativeLang === 'zh-TW')) {
      return true;
    }
    return detectedLang === nativeLang;
  }

  function isCodeText(text) {
    const codePatterns = [
      /^(const|let|var|function|class|import|export|return|if|else|for|while)\s/,
      /[{}();]\s*$/,
      /^\s*(\/\/|\/\*|\*|#)/,
      /\w+\.\w+\(/,
      /console\./,
      /https?:\/\//
    ];
    return codePatterns.some(pattern => pattern.test(text.trim()));
  }

  // 重建文本，只保留指定的词汇（用于发送给 AI）
  function reconstructTextWithWords(text, targetWords) {
    const targetWordSet = new Set(targetWords.map(w => w.toLowerCase()));
    const sentences = text.split(/[.!?]+/).filter(s => s.trim().length > 0);
    const chineseTargets = Array.from(targetWordSet).filter(w => /[\u4e00-\u9fff]/.test(w));

    const relevantSentences = sentences.filter(sentence => {
      const lowerSentence = sentence.toLowerCase();
      // 检查英文单词
      const words = sentence.match(/\b[a-zA-Z]{5,}\b/g) || [];
      const hasEnglishMatch = words.some(word => targetWordSet.has(word.toLowerCase()));
      
      // 检查中文短语（直接检查是否包含目标词汇）
      const hasChineseMatch = chineseTargets.some(word => lowerSentence.includes(word));
      
      return hasEnglishMatch || hasChineseMatch;
    });

    return relevantSentences.join('. ').trim() + (relevantSentences.length > 0 ? '.' : '');
  }

  function parseCacheKey(key) {
    if (!key || typeof key !== 'string') return null;
    const last = key.lastIndexOf(':');
    if (last <= 0) return null;
    const secondLast = key.lastIndexOf(':', last - 1);
    if (secondLast <= 0) return null;
    return {
      word: key.slice(0, secondLast),
      sourceLang: key.slice(secondLast + 1, last),
      targetLang: key.slice(last + 1)
    };
  }

  function makeCacheKey(originalLower, sourceLang, targetLang) {
    return `${originalLower}:${sourceLang}:${targetLang}`;
  }

  function removeFromCjkIndex(cacheKey) {
    const parsed = parseCacheKey(cacheKey);
    if (!parsed?.word || !/[\u4e00-\u9fff]/.test(parsed.word) || parsed.word.length < 2) return;
    const pairKey = `${parsed.sourceLang}:${parsed.targetLang}`;
    const set = cachedCjkWordsByLangPair.get(pairKey);
    if (!set) return;
    set.delete(parsed.word.toLowerCase());
    if (set.size === 0) cachedCjkWordsByLangPair.delete(pairKey);
  }

  function deleteWordCacheKey(cacheKey) {
    if (!wordCache.has(cacheKey)) return;
    wordCache.delete(cacheKey);
    removeFromCjkIndex(cacheKey);
  }

  function evictWordCacheToMaxSize(maxSize) {
    const limit = Math.max(1, Number(maxSize) || DEFAULT_CACHE_MAX_SIZE);
    while (wordCache.size >= limit) {
      const firstKey = wordCache.keys().next().value;
      if (!firstKey) break;
      deleteWordCacheKey(firstKey);
    }
  }

  function upsertWordCacheItem(item, sourceLang, targetLang) {
    if (!item?.original) return;
    const original = String(item.original);
    const originalLower = original.toLowerCase();
    const cacheKey = makeCacheKey(originalLower, sourceLang, targetLang);

    if (wordCache.has(cacheKey)) {
      // LRU: reinsert
      wordCache.delete(cacheKey);
    }

    evictWordCacheToMaxSize(config?.cacheMaxSize || DEFAULT_CACHE_MAX_SIZE);

    wordCache.set(cacheKey, {
      translation: item.translation,
      phonetic: item.phonetic || '',
      difficulty: item.difficulty || 'B1'
    });

    if (/[\u4e00-\u9fff]/.test(original) && original.length >= 2) {
      const pairKey = `${sourceLang}:${targetLang}`;
      const set = cachedCjkWordsByLangPair.get(pairKey) || new Set();
      set.add(originalLower);
      cachedCjkWordsByLangPair.set(pairKey, set);
    }
  }

  function escapeHtml(value) {
    return String(value ?? '')
      .replace(/&/g, '&amp;')
      .replace(/</g, '&lt;')
      .replace(/>/g, '&gt;')
      .replace(/"/g, '&quot;')
      .replace(/'/g, '&#39;');
  }

  function normalizeWordQueryText(word) {
    const cleaned = String(word ?? '').replace(/\s+/g, ' ').trim();
    if (!cleaned) return '';
    return cleaned.slice(0, 80);
  }

  function makeWordQueryCacheKey(word) {
    const normalized = normalizeWordQueryText(word).toLowerCase();
    if (!normalized) return '';
    // v2: bilingual meanings (en+zh)
    return `v2:${normalized}`;
  }

  function evictWordQueryCacheToMaxSize(maxSize) {
    const limit = Math.max(1, Number(maxSize) || DEFAULT_WORD_QUERY_CACHE_MAX_SIZE);
    while (wordQueryCache.size >= limit) {
      const firstKey = wordQueryCache.keys().next().value;
      if (!firstKey) break;
      wordQueryCache.delete(firstKey);
    }
  }

  function upsertWordQueryCacheItem(key, data) {
    if (!key || !data) return;
    if (wordQueryCache.has(key)) wordQueryCache.delete(key); // LRU: reinsert
    evictWordQueryCacheToMaxSize(DEFAULT_WORD_QUERY_CACHE_MAX_SIZE);
    wordQueryCache.set(key, { data, savedAt: Date.now() });
  }

  async function loadWordQueryCache() {
    return new Promise((resolve) => {
      chrome.storage.local.get(WORD_QUERY_CACHE_STORAGE_KEY, (result) => {
        wordQueryCache.clear();
        const cached = result?.[WORD_QUERY_CACHE_STORAGE_KEY];
        if (cached && Array.isArray(cached)) {
          cached.forEach(item => {
            if (!item?.key || !item?.data) return;
            wordQueryCache.set(String(item.key), { data: item.data, savedAt: item.savedAt || 0 });
          });
        }
        resolve(wordQueryCache);
      });
    });
  }

  async function saveWordQueryCache() {
    const data = [];
    for (const [key, value] of wordQueryCache) {
      data.push({ key, data: value.data, savedAt: value.savedAt || 0 });
    }
    return new Promise((resolve, reject) => {
      chrome.storage.local.set({ [WORD_QUERY_CACHE_STORAGE_KEY]: data }, () => {
        if (chrome.runtime.lastError) {
          console.error('[VocabMeld] Failed to save word query cache:', chrome.runtime.lastError);
          reject(chrome.runtime.lastError);
        } else {
          resolve();
        }
      });
    });
  }

  function scheduleSaveWordQueryCache(delay = 600) {
    clearTimeout(wordQueryCacheSaveTimer);
    wordQueryCacheSaveTimer = setTimeout(() => {
      saveWordQueryCache().catch(() => {});
    }, delay);
  }

  function notifyWordQueryListeners(entry, kind, payload) {
    if (!entry?.listeners || entry.listeners.size === 0) return;
    for (const listener of Array.from(entry.listeners)) {
      try {
        if (kind === 'partial' && typeof listener.onPartialData === 'function') {
          listener.onPartialData(payload);
        } else if (kind === 'raw' && typeof listener.onRawText === 'function') {
          listener.onRawText(payload);
        } else if (kind === 'done' && typeof listener.onDone === 'function') {
          listener.onDone(payload);
        } else if (kind === 'error' && typeof listener.onError === 'function') {
          listener.onError(payload);
        }
      } catch {}
    }
  }

  // ============ 词典解释（有道 / Wiktionary） ============
  function scheduleDictCachePersist(delay = 500) {
    if (dictPersistTimer) clearTimeout(dictPersistTimer);
    dictPersistTimer = setTimeout(() => {
      dictPersistTimer = null;
      if (!persistentDictCache) return;
      const data = [];
      for (const [key, value] of persistentDictCache) data.push({ key, value });
      chrome.storage.local.set({ [DICT_CACHE_STORAGE_KEY]: data }, () => {});
    }, delay);
  }

  async function ensureDictCacheLoaded() {
    if (persistentDictCache) return;
    if (dictCacheInitPromise) return dictCacheInitPromise;
    dictCacheInitPromise = new Promise((resolve) => {
      chrome.storage.local.get(DICT_CACHE_STORAGE_KEY, (result) => {
        const raw = result?.[DICT_CACHE_STORAGE_KEY];
        persistentDictCache = new Map();
        if (Array.isArray(raw)) {
          for (const item of raw) {
            if (!item || typeof item.key !== 'string') continue;
            persistentDictCache.set(item.key, item.value ?? null);
          }
        }
        while (persistentDictCache.size > DICT_CACHE_MAX_SIZE) {
          const firstKey = persistentDictCache.keys().next().value;
          persistentDictCache.delete(firstKey);
        }
        resolve();
      });
    }).finally(() => {
      dictCacheInitPromise = null;
    });
    return dictCacheInitPromise;
  }

  async function getDictCacheValue(cacheKey) {
    await ensureDictCacheLoaded();
    if (!persistentDictCache?.has(cacheKey)) return undefined;
    const value = persistentDictCache.get(cacheKey);
    // LRU: move to tail
    persistentDictCache.delete(cacheKey);
    persistentDictCache.set(cacheKey, value);
    return value;
  }

  async function setDictCacheValue(cacheKey, value) {
    await ensureDictCacheLoaded();
    if (!persistentDictCache) persistentDictCache = new Map();
    if (persistentDictCache.has(cacheKey)) persistentDictCache.delete(cacheKey);
    while (persistentDictCache.size >= DICT_CACHE_MAX_SIZE) {
      const firstKey = persistentDictCache.keys().next().value;
      persistentDictCache.delete(firstKey);
    }
    persistentDictCache.set(cacheKey, value ?? null);
    scheduleDictCachePersist();
  }

  function touchDictMemoryCache(cacheKey, value) {
    if (dictCache.has(cacheKey)) dictCache.delete(cacheKey);
    dictCache.set(cacheKey, value ?? null);
    while (dictCache.size > DICT_CACHE_MAX_SIZE) {
      const firstKey = dictCache.keys().next().value;
      dictCache.delete(firstKey);
    }
  }

  function fetchProxyJson(url) {
    return new Promise((resolve, reject) => {
      chrome.runtime.sendMessage({ action: 'fetchProxy', url }, (res) => {
        if (chrome.runtime.lastError) {
          reject(new Error(chrome.runtime.lastError.message));
        } else if (!res?.success) {
          reject(new Error(res?.error || 'Fetch failed'));
        } else {
          resolve(res.data);
        }
      });
    });
  }

  async function fetchYoudaoData(word) {
    try {
      const url = `https://dict.youdao.com/jsonapi?q=${encodeURIComponent(word)}&doctype=json`;
      const response = await fetchProxyJson(url);
      const ecData = response?.ec?.word?.[0];
      if (!ecData) return null;

      const phonetic = ecData.usphone ? `/${ecData.usphone}/` : (ecData.ukphone ? `/${ecData.ukphone}/` : '');

      const meanings = [];
      const trs = ecData.trs || [];
      for (const tr of trs.slice(0, 3)) {
        const defText = tr.tr?.[0]?.l?.i?.[0] || '';
        if (!defText) continue;
        const match = defText.match(/^([a-z]+\.)\s*(.+)$/i);
        if (match) {
          const pos = match[1];
          const def = match[2];
          const existing = meanings.find(m => m.partOfSpeech === pos);
          if (existing) {
            if (existing.definitions.length < 3) existing.definitions.push(def);
          } else {
            meanings.push({ partOfSpeech: pos, definitions: [def] });
          }
        } else {
          meanings.push({ partOfSpeech: '', definitions: [defText] });
        }
      }

      if (meanings.length === 0) return null;
      return { word, phonetic, meanings };
    } catch (e) {
      console.error('[VocabMeld] Youdao fetch error:', e);
      return null;
    }
  }

  async function fetchWiktionaryData(word) {
    try {
      const url = `https://en.wiktionary.org/w/api.php?action=parse&page=${encodeURIComponent(word)}&format=json&prop=text&origin=*`;
      const data = await fetchProxyJson(url);
      if (data?.error || !data?.parse?.text?.['*']) return null;

      const htmlString = data.parse.text['*'];
      const parser = new DOMParser();
      const doc = parser.parseFromString(htmlString, 'text/html');
      const contentRoot = doc.querySelector('.mw-parser-output') || doc.body;

      const phoneticEl = contentRoot.querySelector('.IPA');
      const phonetic = phoneticEl?.textContent?.trim() || '';

      const validPOS = [
        'Noun',
        'Verb',
        'Adjective',
        'Adverb',
        'Interjection',
        'Pronoun',
        'Preposition',
        'Conjunction'
      ];

      const meaningsMap = new Map();
      const headers = contentRoot.querySelectorAll('h3, h4');
      for (const header of headers) {
        const headerText = header.textContent.replace(/\[.*?\]/g, '').trim();
        const matchedPOS = validPOS.find(pos => headerText.includes(pos));
        if (!matchedPOS) continue;

        let currentNode = header.parentNode?.classList?.contains('mw-heading') ? header.parentNode : header;
        let definitionList = null;
        while (currentNode?.nextElementSibling) {
          currentNode = currentNode.nextElementSibling;
          if (currentNode.tagName === 'OL') {
            definitionList = currentNode;
            break;
          }
          if (['H2', 'H3', 'H4'].includes(currentNode.tagName)) break;
        }
        if (!definitionList) continue;

        const listItems = definitionList.querySelectorAll(':scope > li');
        for (const li of Array.from(listItems).slice(0, 2)) {
          const cloneLi = li.cloneNode(true);
          cloneLi
            .querySelectorAll('.h-usage-example, .e-example, ul, dl, .reference, .citation')
            .forEach(el => el.remove());
          const defText = cloneLi.textContent.replace(/<[^>]*>/g, '').trim().slice(0, 150);
          if (!defText) continue;
          if (!meaningsMap.has(matchedPOS)) meaningsMap.set(matchedPOS, []);
          const defs = meaningsMap.get(matchedPOS);
          if (defs.length < 3) defs.push(defText);
        }
      }

      const meanings = [];
      for (const [pos, defs] of meaningsMap) {
        if (meanings.length >= 3) break;
        if (defs.length > 0) meanings.push({ partOfSpeech: pos, definitions: defs });
      }

      if (meanings.length === 0) return null;
      return { word, phonetic, meanings };
    } catch (e) {
      console.error('[VocabMeld] Wiktionary fetch error:', e);
      return null;
    }
  }

  async function fetchDictionaryData(word) {
    const cleaned = normalizeWordQueryText(word);
    if (!cleaned) return null;
    const dictionaryType = config?.dictionaryType || 'zh-en';
    const cacheKey = `${cleaned.toLowerCase()}_${dictionaryType}`;

    // 1) memory cache
    if (dictCache.has(cacheKey)) return dictCache.get(cacheKey);

    // 2) persisted cache
    const persisted = await getDictCacheValue(cacheKey);
    if (persisted !== undefined) {
      touchDictMemoryCache(cacheKey, persisted);
      return persisted;
    }

    try {
      const result = dictionaryType === 'zh-en'
        ? await fetchYoudaoData(cleaned)
        : await fetchWiktionaryData(cleaned);
      touchDictMemoryCache(cacheKey, result);
      await setDictCacheValue(cacheKey, result);
      return result;
    } catch (e) {
      console.error('[VocabMeld] Dictionary fetch error:', e);
      touchDictMemoryCache(cacheKey, null);
      setDictCacheValue(cacheKey, null);
      return null;
    }
  }

  function buildTooltipDictHtmlLoading(word) {
    const shown = escapeHtml(word || '');
    return `
      <div class="vocabmeld-tooltip-dict-title">词典解释</div>
      ${shown ? `<div class="vocabmeld-tooltip-dict-word">${shown}</div>` : ''}
      <div class="vocabmeld-dict-loading">加载词典...</div>
    `;
  }

  function buildTooltipDictHtmlUnsupported(word) {
    const shown = escapeHtml(word || '');
    return `
      <div class="vocabmeld-tooltip-dict-title">词典解释</div>
      ${shown ? `<div class="vocabmeld-tooltip-dict-word">${shown}</div>` : ''}
      <div class="vocabmeld-dict-empty">仅支持英文单词</div>
    `;
  }

  function buildTooltipDictHtmlEmpty(word) {
    const shown = escapeHtml(word || '');
    return `
      <div class="vocabmeld-tooltip-dict-title">词典解释</div>
      ${shown ? `<div class="vocabmeld-tooltip-dict-word">${shown}</div>` : ''}
      <div class="vocabmeld-dict-empty">暂无词典数据</div>
    `;
  }

  function buildTooltipDictHtmlError(word, message) {
    const shown = escapeHtml(word || '');
    return `
      <div class="vocabmeld-tooltip-dict-title">词典解释</div>
      ${shown ? `<div class="vocabmeld-tooltip-dict-word">${shown}</div>` : ''}
      <div class="vocabmeld-dict-empty">加载失败：${escapeHtml(message || '')}</div>
    `;
  }

  function buildTooltipDictHtmlData(dictData) {
    if (!dictData?.meanings?.length) return buildTooltipDictHtmlEmpty(dictData?.word || '');
    const word = escapeHtml(dictData.word || '');
    const phonetic = escapeHtml(dictData.phonetic || '');
    let html = `
      <div class="vocabmeld-tooltip-dict-title">词典解释</div>
      ${word ? `<div class="vocabmeld-tooltip-dict-word">${word}</div>` : ''}
      ${phonetic ? `<div class="vocabmeld-tooltip-dict-phonetic">${phonetic}</div>` : ''}
    `;

    for (const meaning of dictData.meanings) {
      html += `<div class="vocabmeld-dict-entry">`;
      if (meaning.partOfSpeech) {
        html += `<span class="vocabmeld-dict-pos">${escapeHtml(meaning.partOfSpeech)}</span>`;
      }
      html += `<ul class="vocabmeld-dict-defs">`;
      for (const def of meaning.definitions || []) {
        html += `<li>${escapeHtml(def)}</li>`;
      }
      html += `</ul></div>`;
    }
    return html;
  }

  function normalizeSiteRuleList(value) {
    const items = Array.isArray(value)
      ? value
      : (typeof value === 'string' ? value.split(/\r?\n|,/g) : []);

    return items
      .map((item) => String(item || '').trim().toLowerCase())
      .filter(Boolean)
      .map((item) => {
        // Allow partial match, but strip protocol/path if user pasted a URL.
        let s = item.replace(/^[a-z]+:\/\//i, '');
        s = s.split('/')[0] || '';
        return s.trim();
      })
      .filter(Boolean);
  }

  function shouldProcessSite(hostname = window.location.hostname) {
    if (!config?.enabled) return false;
    const host = String(hostname || '').toLowerCase();
    if (!host) return true;

    if ((config.siteMode || 'all') === 'all') {
      const excluded = config.excludedSites || [];
      return !excluded.some((domain) => domain && host.includes(domain));
    }

    const allowed = config.allowedSites || [];
    if (allowed.length === 0) return false;
    return allowed.some((domain) => domain && host.includes(domain));
  }

  // ============ 存储操作 ============
  async function loadConfig() {
    return new Promise((resolve) => {
      chrome.storage.sync.get(null, (result) => {
        config = {
          apiEndpoint: result.apiEndpoint || 'https://api.deepseek.com/chat/completions',
          apiKey: result.apiKey || '',
          modelName: result.modelName || 'deepseek-chat',
          translationApiConfig: result.translationApiConfig || result.currentApiConfig || '',
          queryApiEndpoint: result.queryApiEndpoint || result.apiEndpoint || 'https://api.deepseek.com/chat/completions',
          queryApiKey: result.queryApiKey || result.apiKey || '',
          queryModelName: result.queryModelName || result.modelName || 'deepseek-chat',
          queryApiConfig: result.queryApiConfig || result.translationApiConfig || result.currentApiConfig || '',
          enableWordQuery: result.enableWordQuery ?? false,
          wordQueryDefinitionDisplay: result.wordQueryDefinitionDisplay || 'both',
          dictionaryType: result.dictionaryType || 'zh-en',
          nativeLanguage: result.nativeLanguage || 'zh-CN',
          targetLanguage: result.targetLanguage || 'en',
          difficultyLevel: result.difficultyLevel || 'B1',
          intensity: result.intensity || 'medium',
          processMode: result.processMode || 'both',
          autoProcess: result.autoProcess ?? false,
          showPhonetic: result.showPhonetic ?? true,
          showAddMemorize: result.showAddMemorize ?? true,
          cacheMaxSize: result.cacheMaxSize || DEFAULT_CACHE_MAX_SIZE,
          translationStyle: result.translationStyle || 'translation-original',
          theme: result.theme || 'dark',
          enabled: result.enabled ?? true,
          sentenceTranslationRate: result.sentenceTranslationRate ?? DEFAULT_SENTENCE_TRANSLATION_RATE,
          paragraphTranslationRate: result.paragraphTranslationRate ?? DEFAULT_PARAGRAPH_TRANSLATION_RATE,
          siteMode: result.siteMode || 'all',
          excludedSites: normalizeSiteRuleList(result.excludedSites || result.blacklist || []),
          allowedSites: normalizeSiteRuleList(result.allowedSites || []),
          learnedWords: result.learnedWords || [],
          memorizeList: result.memorizeList || []
        };
        resolve(config);
      });
    });
  }

  // 更新 UI 元素的主题
  function updateUITheme() {
    const theme = config?.theme || 'dark';
    if (tooltip) {
      tooltip.setAttribute('data-theme', theme);
    }
    if (selectionPopup) {
      selectionPopup.setAttribute('data-theme', theme);
    }
  }

  async function loadWordCache() {
    return new Promise((resolve) => {
      chrome.storage.local.get('vocabmeld_word_cache', (result) => {
        wordCache.clear();
        cachedCjkWordsByLangPair = new Map();
        const cached = result.vocabmeld_word_cache;
        if (cached && Array.isArray(cached)) {
          cached.forEach(item => {
            wordCache.set(item.key, {
              translation: item.translation,
              phonetic: item.phonetic,
              difficulty: item.difficulty
            });

            const parsed = parseCacheKey(item.key);
            if (parsed?.word && /[\u4e00-\u9fff]/.test(parsed.word) && parsed.word.length >= 2) {
              const pairKey = `${parsed.sourceLang}:${parsed.targetLang}`;
              const set = cachedCjkWordsByLangPair.get(pairKey) || new Set();
              set.add(parsed.word.toLowerCase());
              cachedCjkWordsByLangPair.set(pairKey, set);
            }
          });
        }
        resolve(wordCache);
      });
    });
  }

  async function saveWordCache() {
    const data = [];
    for (const [key, value] of wordCache) {
      data.push({ key, ...value });
    }
    return new Promise((resolve, reject) => {
      chrome.storage.local.set({ vocabmeld_word_cache: data }, () => {
        if (chrome.runtime.lastError) {
          console.error('[VocabMeld] Failed to save cache:', chrome.runtime.lastError);
          reject(chrome.runtime.lastError);
        } else {
          resolve();
        }
      });
    });
  }

  async function updateStats(stats) {
    return new Promise((resolve) => {
      chrome.storage.sync.get(['totalWords', 'todayWords', 'lastResetDate', 'cacheHits', 'cacheMisses'], (current) => {
        const today = new Date().toISOString().split('T')[0];
        if (current.lastResetDate !== today) {
          current.todayWords = 0;
          current.lastResetDate = today;
        }
        const updated = {
          totalWords: (current.totalWords || 0) + (stats.newWords || 0),
          todayWords: (current.todayWords || 0) + (stats.newWords || 0),
          lastResetDate: today,
          cacheHits: (current.cacheHits || 0) + (stats.cacheHits || 0),
          cacheMisses: (current.cacheMisses || 0) + (stats.cacheMisses || 0)
        };
        chrome.storage.sync.set(updated, () => resolve(updated));
      });
    });
  }

  async function addToWhitelist(original, translation, difficulty) {
    const whitelist = config.learnedWords || [];
    const exists = whitelist.some(w => w.original === original || w.word === translation);
    if (!exists) {
      whitelist.push({ 
        original, 
        word: translation, 
        addedAt: Date.now(),
        difficulty: difficulty || 'B1'
      });
      config.learnedWords = whitelist;
      await new Promise(resolve => chrome.storage.sync.set({ learnedWords: whitelist }, resolve));
    }
  }

  async function addToMemorizeList(word) {
    if (!word || !word.trim()) {
      console.warn('[VocabMeld] Invalid word for memorize list:', word);
      return;
    }

    const trimmedWord = word.trim();
    const trimmedLower = trimmedWord.toLowerCase();
    const list = config.memorizeList || [];
    const exists = list.some(w => String(w.word || '').trim().toLowerCase() === trimmedLower);
    
    if (!exists) {
      list.push({ word: trimmedWord, addedAt: Date.now() });
      config.memorizeList = list;
      await new Promise(resolve => chrome.storage.sync.set({ memorizeList: list }, resolve));

      // 添加到记忆列表后，立即检查页面上是否存在这些单词并触发翻译
      // 确保配置已加载且扩展已启用
      if (!config) {
        await loadConfig();
      }
      
      // 确保扩展已启用
      if (!config.enabled) {
        showToast(`"${trimmedWord}" 已添加到记忆列表`);
        return;
      }
      
      // 立即触发翻译处理（等待完成以确保翻译结果正确应用到页面）
      try {
        const count = await processSpecificWords([trimmedWord]);
        
        if (count > 0) {
          showToast(`"${trimmedWord}" 已添加到记忆列表并翻译`);
        } else {
          // 即使页面上没有找到，也要确保翻译结果被缓存，以便下次加载时使用
          try {
            await translateSpecificWords([trimmedWord]);
            showToast(`"${trimmedWord}" 已添加到记忆列表`);
          } catch (error) {
            console.error('[VocabMeld] Error translating word:', trimmedWord, error);
            showToast(`"${trimmedWord}" 已添加到记忆列表`);
          }
        }
      } catch (error) {
        console.error('[VocabMeld] Error processing word:', trimmedWord, error);
        showToast(`"${trimmedWord}" 已添加到记忆列表`);
      }
    } else {
      showToast(`"${trimmedWord}" 已在记忆列表中`);
    }
  }

  async function removeFromMemorizeList(word) {
    if (!word || !word.trim()) return;
    const trimmedWord = word.trim();
    const trimmedLower = trimmedWord.toLowerCase();
    const list = config.memorizeList || [];
    const newList = list.filter(w => String(w.word || '').trim().toLowerCase() !== trimmedLower);
    if (newList.length === list.length) return;
    config.memorizeList = newList;
    await new Promise(resolve => chrome.storage.sync.set({ memorizeList: newList }, resolve));
    showToast(`"${trimmedWord}" 已从记忆列表移除`);
  }

  // ============ DOM 处理 ============
  function shouldSkipNode(node, skipStyleCheck = false) {
    if (!node) return true;
    if (node.nodeType !== Node.ELEMENT_NODE && node.nodeType !== Node.TEXT_NODE) return true;
    if (node.nodeType === Node.TEXT_NODE) return shouldSkipNode(node.parentElement, skipStyleCheck);

    const element = node;
    if (SKIP_TAGS.includes(element.tagName)) return true;
    const classList = element.className?.toString() || '';
    if (SKIP_CLASSES.some(cls => classList.includes(cls))) return true;

    // 使用更轻量的可见性检测，避免频繁触发 getComputedStyle
    if (!skipStyleCheck) {
      // 使用 offsetParent 快速检测是否隐藏（display: none 的元素 offsetParent 为 null）
      // 注意：position: fixed 元素的 offsetParent 也是 null，但这些通常不需要处理
      if (element.offsetParent === null && element.tagName !== 'BODY' && element.tagName !== 'HTML') {
        // 排除 position: fixed 的情况
        const position = element.style.position;
        if (position !== 'fixed' && position !== 'sticky') {
          return true;
        }
      }
    }

    if (element.isContentEditable) return true;
    if (element.hasAttribute('data-vocabmeld-processed')) return true;

    return false;
  }

  function getElementPath(element) {
    const parts = [];
    let current = element;
    while (current && current !== document.body) {
      let selector = current.tagName?.toLowerCase() || '';
      if (current.id) selector += `#${current.id}`;
      parts.unshift(selector);
      current = current.parentElement;
    }
    return parts.join('>');
  }

  function findTextContainers(root) {
    // Build containers by walking text nodes and mapping them to a preferred ancestor container.
    // This avoids missing content on pages where text is wrapped in spans (no direct text nodes).
    const containers = new Set();
    const preferredTags = new Set([
      'P', 'LI', 'TD', 'TH', 'ARTICLE', 'SECTION', 'BLOCKQUOTE',
      'H1', 'H2', 'H3', 'H4', 'H5', 'H6', 'DIV'
    ]);

    const walker = document.createTreeWalker(root, NodeFilter.SHOW_TEXT, {
      acceptNode: (node) => {
        const parent = node.parentElement;
        if (!parent) return NodeFilter.FILTER_REJECT;
        if (shouldSkipNode(parent, true)) return NodeFilter.FILTER_REJECT;
        const text = (node.textContent || '').trim();
        if (text.length < 10) return NodeFilter.FILTER_REJECT;
        if (isCodeText(text)) return NodeFilter.FILTER_REJECT;
        return NodeFilter.FILTER_ACCEPT;
      }
    });

    let textNode;
    while (textNode = walker.nextNode()) {
      let current = textNode.parentElement;
      if (!current) continue;

      let spanFallback = null;
      while (current && current !== document.body) {
        if (shouldSkipNode(current, true)) break;

        if (preferredTags.has(current.tagName)) {
          containers.add(current);
          break;
        }

        if (TEXT_CONTAINER_TAGS.has(current.tagName)) {
          if (current.tagName === 'SPAN') {
            spanFallback = current;
          } else {
            containers.add(current);
            break;
          }
        }

        current = current.parentElement;
      }

      if ((!current || current === document.body) && spanFallback) {
        containers.add(spanFallback);
      }
    }

    return Array.from(containers);
  }

  function getTextContent(element) {
    const texts = [];
    const walker = document.createTreeWalker(element, NodeFilter.SHOW_TEXT, {
      acceptNode: (node) => {
        if (shouldSkipNode(node.parentElement)) return NodeFilter.FILTER_REJECT;
        const text = node.textContent.trim();
        if (text.length > 0 && !isCodeText(text)) return NodeFilter.FILTER_ACCEPT;
        return NodeFilter.FILTER_REJECT;
      }
    });

    let node;
    while (node = walker.nextNode()) texts.push(node.textContent);
    return texts.join(' ').replace(/\s+/g, ' ').trim();
  }

  const MAX_SEGMENTS_PER_BATCH = 20; // 每批最多处理的段落数

  function getPageSegments(viewportOnly = false, margin = 500) {
    const segments = [];
    let viewportTop = 0, viewportBottom = Infinity;
    
    if (viewportOnly) {
      viewportTop = window.scrollY - margin;
      viewportBottom = window.scrollY + window.innerHeight + margin;
    }

    const containers = findTextContainers(document.body);

    for (const container of containers) {
      // 已达到批次上限，停止添加
      if (segments.length >= MAX_SEGMENTS_PER_BATCH) break;

      if (viewportOnly) {
        const rect = container.getBoundingClientRect();
        const elementTop = rect.top + window.scrollY;
        const elementBottom = rect.bottom + window.scrollY;
        if (elementBottom < viewportTop || elementTop > viewportBottom) continue;
      }

      const text = getTextContent(container);
      const minLen = isLikelyBilibiliCommentContainer(container) ? 10 : 50;
      if (!text || text.length < minLen) continue;
      if (isCodeText(text)) continue;

      const path = getElementPath(container);
      const fingerprint = generateFingerprint(text, path);
      if (processedFingerprints.has(fingerprint)) continue;

      segments.push({ element: container, text: text.slice(0, 2000), fingerprint, path });
    }

    return segments;
  }

  // ============ 文本替换 ============
  function createReplacementElement(original, translation, phonetic, difficulty) {
    const wrapper = document.createElement('span');
    wrapper.className = 'vocabmeld-translated';
    wrapper.setAttribute('data-original', original);
    wrapper.setAttribute('data-translation', translation);
    wrapper.setAttribute('data-phonetic', phonetic || '');
    wrapper.setAttribute('data-difficulty', difficulty || 'B1');
    
    // 根据配置的样式生成不同的HTML
    const style = config.translationStyle || 'translation-original';
    let innerHTML = '';
    
    switch (style) {
      case 'translation-only':
        // 只显示译文
        innerHTML = `<span class="vocabmeld-word">${translation}</span>`;
        break;
      case 'original-translation':
        // 原文(译文)
        innerHTML = `<span class="vocabmeld-original">${original}</span><span class="vocabmeld-word">(${translation})</span>`;
        break;
      case 'translation-original':
      default:
        // 译文(原文) - 默认样式
        innerHTML = `<span class="vocabmeld-word">${translation}</span><span class="vocabmeld-original">(${original})</span>`;
        break;
    }
    
    wrapper.innerHTML = innerHTML;
    return wrapper;
  }

  function applyReplacements(element, replacements) {
    if (!element || !replacements?.length) return 0;
    // 段落已整体翻译为目标语言时，不再做词级替换
    if (element.hasAttribute('data-vocabmeld-paragraph-translated')) return 0;

    let count = 0;
    
    // 获取文本节点的辅助函数（每次调用都重新获取，确保节点引用有效）
    function getTextNodes() {
      const nodes = [];
      const walker = document.createTreeWalker(element, NodeFilter.SHOW_TEXT, {
        acceptNode: (node) => {
          const parent = node.parentElement;
          if (!parent) return NodeFilter.FILTER_REJECT;
          
          // 跳过已做句子/段落整体翻译的区域（避免在已翻译区域内再做词级替换）
          if (parent.closest?.('.vocabmeld-segment-translated, .vocabmeld-paragraph-original, .vocabmeld-paragraph-translated')) {
            return NodeFilter.FILTER_REJECT;
          }

          // 跳过已翻译的元素
          if (parent.classList?.contains('vocabmeld-translated')) {
            return NodeFilter.FILTER_REJECT;
          }
          
          // 跳过不应该处理的节点类型
          if (SKIP_TAGS.includes(parent.tagName)) return NodeFilter.FILTER_REJECT;
          
          // 跳过代码相关的类
          const classList = parent.className?.toString() || '';
          if (SKIP_CLASSES.some(cls => classList.includes(cls) && cls !== 'vocabmeld-translated')) {
            return NodeFilter.FILTER_REJECT;
          }
          
          // 跳过隐藏元素（使用 offsetParent 快速检测）
          if (parent.offsetParent === null && parent.tagName !== 'BODY' && parent.tagName !== 'HTML') {
            const position = parent.style.position;
            if (position !== 'fixed' && position !== 'sticky') {
              return NodeFilter.FILTER_REJECT;
            }
          }
          
          // 跳过可编辑元素
          if (parent.isContentEditable) return NodeFilter.FILTER_REJECT;
          
          const text = node.textContent.trim();
          if (text.length === 0) return NodeFilter.FILTER_REJECT;
          
          return NodeFilter.FILTER_ACCEPT;
        }
      });
      
      let node;
      while (node = walker.nextNode()) {
        nodes.push(node);
      }
      return nodes;
    }

    // 按位置从后往前排序，避免位置偏移问题
    const sortedReplacements = [...replacements].sort((a, b) => (b.position || 0) - (a.position || 0));

    for (const replacement of sortedReplacements) {
      const { original, translation, phonetic, difficulty } = replacement;
      const lowerOriginal = original.toLowerCase();
      
      // 每次替换后重新获取文本节点，因为DOM结构已改变
      const textNodes = getTextNodes();
      
      for (let i = 0; i < textNodes.length; i++) {
        const textNode = textNodes[i];
        
        // 检查节点是否仍然有效（DOM可能已改变）
        if (!textNode.parentElement || !element.contains(textNode)) {
          continue;
        }
        
        const text = textNode.textContent;
        const lowerText = text.toLowerCase();
        
        // 检查文本节点是否包含目标单词
        if (!lowerText.includes(lowerOriginal)) continue;
        
        // 使用单词边界匹配，确保匹配完整单词
        const escapedOriginal = original.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
        // 匹配单词边界（包括中文标点）
        const regex = new RegExp(`(^|[^\\w\\u4e00-\\u9fff])${escapedOriginal}([^\\w\\u4e00-\\u9fff]|$)`, 'i');
        
        let match = regex.exec(text);
        let startIndex = match ? match.index + match[1].length : text.toLowerCase().indexOf(lowerOriginal);
        
        if (startIndex === -1) continue;

        try {
          const range = document.createRange();
          range.setStart(textNode, startIndex);
          range.setEnd(textNode, startIndex + original.length);
          
          const rangeContent = range.toString();
          if (rangeContent.toLowerCase() !== lowerOriginal) continue;

          // 检查是否已经被替换（检查父元素是否是已翻译的元素）
          let parent = textNode.parentElement;
          let isAlreadyReplaced = false;
          while (parent && parent !== element) {
            if (parent.classList?.contains('vocabmeld-translated')) {
              isAlreadyReplaced = true;
              break;
            }
            parent = parent.parentElement;
          }
          
          if (isAlreadyReplaced) continue;

          const wrapper = createReplacementElement(original, translation, phonetic, difficulty);
          range.deleteContents();
          range.insertNode(wrapper);
          count++;
          
          // 找到匹配后立即跳出，因为DOM结构已改变，需要重新获取节点
          break;
        } catch (e) {
          console.error('[VocabMeld] Replacement error:', e, original);
        }
      }
    }

    if (count > 0) element.setAttribute('data-vocabmeld-processed', 'true');
    return count;
  }

  function restoreOriginal(element) {
    if (!element.classList?.contains('vocabmeld-translated')) return;
    const original = element.getAttribute('data-original');
    const textNode = document.createTextNode(original);
    element.parentNode.replaceChild(textNode, element);
  }

  // 恢复页面上所有相同单词的原文
  function restoreAllSameWord(originalWord) {
    document.querySelectorAll('.vocabmeld-translated').forEach(el => {
      if (el.getAttribute('data-original')?.toLowerCase() === originalWord.toLowerCase()) {
        restoreOriginal(el);
      }
    });
  }

  function restoreSegmentTranslation(wrapper) {
    if (!wrapper?.classList?.contains('vocabmeld-segment-translated')) return;
    const originalContent = wrapper.querySelector('.vocabmeld-segment-original-content');
    if (!originalContent) {
      wrapper.remove();
      return;
    }

    const nodes = Array.from(originalContent.childNodes);
    if (nodes.length > 0) {
      wrapper.replaceWith(...nodes);
    } else {
      wrapper.replaceWith(document.createTextNode(''));
    }
  }

  function restoreAllSegmentTranslations(root = document) {
    root.querySelectorAll('.vocabmeld-segment-translated').forEach(restoreSegmentTranslation);
  }

  function restoreParagraphTranslation(element) {
    if (!element?.hasAttribute?.('data-vocabmeld-paragraph-translated')) return;
    const originalContent = element.querySelector('.vocabmeld-paragraph-original-content');
    if (!originalContent) {
      element.removeAttribute('data-vocabmeld-paragraph-translated');
      return;
    }

    const fragment = document.createDocumentFragment();
    while (originalContent.firstChild) {
      fragment.appendChild(originalContent.firstChild);
    }

    while (element.firstChild) {
      element.removeChild(element.firstChild);
    }
    element.appendChild(fragment);

    element.removeAttribute('data-vocabmeld-paragraph-translated');
  }

  function restoreAllParagraphTranslations(root = document) {
    root.querySelectorAll('[data-vocabmeld-paragraph-translated]').forEach(restoreParagraphTranslation);
  }

  function restoreAll() {
    restoreAllParagraphTranslations(document);
    restoreAllSegmentTranslations(document);
    document.querySelectorAll('.vocabmeld-translated').forEach(restoreOriginal);
    document.querySelectorAll('[data-vocabmeld-processed]').forEach(el => el.removeAttribute('data-vocabmeld-processed'));
    document.querySelectorAll(`[${SCANNED_ATTR}]`).forEach(el => el.removeAttribute(SCANNED_ATTR));
    document.querySelectorAll('[data-vocabmeld-observing]').forEach(el => el.removeAttribute('data-vocabmeld-observing'));
    document.querySelectorAll(`[${PROCESSING_ATTR}]`).forEach(el => el.removeAttribute(PROCESSING_ATTR));
    processedFingerprints.clear();
    pendingContainers.clear();
  }

  // ============ 句子/段落翻译（额外翻译为学习语言） ============
  function hashToUint32(str) {
    let hash = 2166136261;
    for (let i = 0; i < str.length; i++) {
      hash ^= str.charCodeAt(i);
      hash = Math.imul(hash, 16777619);
    }
    return hash >>> 0;
  }

  function stableUnitRandom(seed) {
    return hashToUint32(seed) / 0xFFFFFFFF;
  }

  function isEligibleForInlineTranslation(element) {
    if (!element?.tagName) return false;
    return INLINE_TRANSLATION_ALLOWED_TAGS.has(element.tagName);
  }

  function getReplaceableTextNodes(element) {
    const nodes = [];
    const walker = document.createTreeWalker(element, NodeFilter.SHOW_TEXT, {
      acceptNode: (node) => {
        const parent = node.parentElement;
        if (!parent) return NodeFilter.FILTER_REJECT;
        if (parent.classList?.contains('vocabmeld-translated')) return NodeFilter.FILTER_REJECT;
        if (parent.classList?.contains('vocabmeld-segment-translated')) return NodeFilter.FILTER_REJECT;
        if (SKIP_TAGS.includes(parent.tagName)) return NodeFilter.FILTER_REJECT;
        const classList = parent.className?.toString() || '';
        if (SKIP_CLASSES.some(cls => classList.includes(cls) && cls !== 'vocabmeld-translated')) {
          return NodeFilter.FILTER_REJECT;
        }
        if (parent.isContentEditable) return NodeFilter.FILTER_REJECT;
        if ((node.textContent || '').length === 0) return NodeFilter.FILTER_REJECT;
        return NodeFilter.FILTER_ACCEPT;
      }
    });

    let node;
    while (node = walker.nextNode()) nodes.push(node);
    return nodes;
  }

  function buildTextIndex(textNodes, maxChars = Infinity) {
    let fullText = '';
    const index = [];

    for (const node of textNodes) {
      if (fullText.length >= maxChars) break;
      const start = fullText.length;
      fullText += node.textContent || '';
      const end = fullText.length;
      index.push({ node, start, end });
    }

    return { fullText, index };
  }

  function getDomPointAtIndex(index, absoluteOffset) {
    for (const entry of index) {
      if (absoluteOffset >= entry.start && absoluteOffset <= entry.end) {
        return { node: entry.node, offset: absoluteOffset - entry.start };
      }
    }
    const last = index[index.length - 1];
    if (!last) return null;
    return { node: last.node, offset: (last.node.textContent || '').length };
  }

  function splitSentenceRanges(fullText) {
    const text = fullText || '';
    if (!text.trim()) return [];

    const cjk = /[\u4e00-\u9fff\u3040-\u30ff\uac00-\ud7af]/.test(text);
    const regex = cjk
      ? /[^。！？!?]+[。！？!?]+|[^。！？!?]+$/g
      : /[^.!?]+[.!?]+|[^.!?]+$/g;

    const ranges = [];
    let match;
    while ((match = regex.exec(text)) !== null) {
      const raw = match[0];
      const rawStart = match.index;
      const rawEnd = rawStart + raw.length;

      // 去掉两侧空白，只替换“句子主体”，避免吞掉段落间空格
      const leftTrim = raw.match(/^\s*/)?.[0]?.length || 0;
      const rightTrim = raw.match(/\s*$/)?.[0]?.length || 0;
      const start = rawStart + leftTrim;
      const end = rawEnd - rightTrim;
      const sentenceText = text.slice(start, end).trim();

      if (sentenceText) {
        ranges.push({ start, end, text: sentenceText });
      }
    }

    return ranges;
  }

  function pickSentencesForTranslation(text, fingerprint) {
    const sentences = splitSentenceRanges(text)
      .map(s => ({ ...s, text: (s.text || '').trim() }))
      .filter(s => s.text.length >= MIN_SENTENCE_CHARS && s.text.length <= MAX_SENTENCE_CHARS);

    if (!sentences.length) return [];

    const scored = sentences.map((s, i) => ({
      ...s,
      score: stableUnitRandom(`${fingerprint}:sentencePick:${i}`)
    }));

    scored.sort((a, b) => a.score - b.score);
    return scored.slice(0, Math.min(MAX_SENTENCE_TRANSLATIONS_PER_PARAGRAPH, scored.length));
  }

  function callApiViaBackground(body) {
    if (document.hidden || !isTabActive) {
      return Promise.reject(new Error('Paused: tab is not active'));
    }
    return new Promise((resolve, reject) => {
      chrome.runtime.sendMessage({
        action: 'apiRequest',
        endpoint: config.apiEndpoint,
        apiKey: config.apiKey,
        body
      }, response => {
        if (chrome.runtime.lastError) {
          reject(new Error(chrome.runtime.lastError.message));
        } else if (!response?.success) {
          reject(new Error(response?.error || 'API request failed'));
        } else {
          resolve(response.data);
        }
      });
    });
  }

  function callApiViaBackgroundWith(endpoint, apiKey, body, { queue } = {}) {
    if (document.hidden || !isTabActive) {
      return Promise.reject(new Error('Paused: tab is not active'));
    }
    return new Promise((resolve, reject) => {
      chrome.runtime.sendMessage({
        action: 'apiRequest',
        endpoint,
        apiKey,
        body,
        queue
      }, response => {
        if (chrome.runtime.lastError) {
          reject(new Error(chrome.runtime.lastError.message));
        } else if (!response?.success) {
          reject(new Error(response?.error || 'API request failed'));
        } else {
          resolve(response.data);
        }
      });
    });
  }

  function extractAssistantText(apiResponse) {
    return (apiResponse?.choices?.[0]?.message?.content || '').trim();
  }

  function createStreamId() {
    return `${Date.now().toString(36)}-${Math.random().toString(36).slice(2)}`;
  }

  function apiRequestStreamViaBackground(endpoint, apiKey, body, { onDelta, onText } = {}) {
    const streamId = createStreamId();
    const port = chrome.runtime.connect({ name: 'vocabmeld-api-stream' });
    let fullText = '';
    let settled = false;
    let canceled = false;
    let lastUiAt = 0;

    const promise = new Promise((resolve, reject) => {
      const handleDisconnect = () => {
        if (settled) return;
        settled = true;
        if (canceled) return reject(new Error('Canceled'));
        reject(new Error('Stream disconnected'));
      };

      port.onDisconnect.addListener(handleDisconnect);

      port.onMessage.addListener((msg) => {
        if (!msg || msg.streamId !== streamId) return;
        if (msg.type === 'apiStreamDelta') {
          const delta = String(msg.delta || '');
          if (!delta) return;
          fullText += delta;
          if (typeof onDelta === 'function') {
            try { onDelta(delta, fullText); } catch {}
          }
          if (typeof onText === 'function') {
            const now = Date.now();
            if (now - lastUiAt >= 80) {
              lastUiAt = now;
              onText(fullText);
            }
          }
          return;
        }
        if (msg.type === 'apiStreamDone') {
          if (settled) return;
          settled = true;
          const text = typeof msg.text === 'string' ? msg.text : fullText;
          if (typeof onText === 'function') onText(text);
          resolve(text);
          try { port.disconnect(); } catch {}
          return;
        }
        if (msg.type === 'apiStreamError') {
          if (settled) return;
          settled = true;
          reject(new Error(msg.error || 'Stream error'));
          try { port.disconnect(); } catch {}
        }
      });

      port.postMessage({ action: 'apiRequestStream', streamId, endpoint, apiKey, body });
    });

    const cancel = () => {
      if (settled) return;
      canceled = true;
      try { port.disconnect(); } catch {}
    };

    return { promise, cancel };
  }

  function tryParseJsonObject(text) {
    const content = String(text || '').trim();
    if (!content) return null;
    try {
      const parsed = JSON.parse(content);
      if (parsed && typeof parsed === 'object' && !Array.isArray(parsed)) return parsed;
    } catch {}
    const match = content.match(/\{[\s\S]*\}/);
    if (!match) return null;
    try {
      const parsed = JSON.parse(match[0]);
      if (parsed && typeof parsed === 'object' && !Array.isArray(parsed)) return parsed;
    } catch {}
    return null;
  }

  function normalizeWordQueryResult(obj, fallbackWord) {
    const word = normalizeWordQueryText(obj?.word || fallbackWord);
    const partsOfSpeech = Array.isArray(obj?.parts_of_speech) ? obj.parts_of_speech.filter(Boolean).map(String) : [];

    const normalizeMeaningList = (raw) => {
      const list = Array.isArray(raw) ? raw : [];
      return list
        .map(m => ({
          pos: String(m?.pos || '').trim(),
          definitions: Array.isArray(m?.definitions) ? m.definitions.filter(Boolean).map(String).slice(0, 8) : []
        }))
        .filter(m => m.pos || m.definitions.length > 0)
        .slice(0, 8);
    };

    // Backward compatible:
    // - old schema: meanings (English only)
    // - new schema: meanings_en + meanings_zh
    const meaningsEn = normalizeMeaningList(obj?.meanings_en || obj?.meaningsEn || obj?.meanings || []);
    const meaningsZh = normalizeMeaningList(obj?.meanings_zh || obj?.meaningsZh || []);
    const inflections = Array.isArray(obj?.inflections) ? obj.inflections.filter(Boolean).map(String).slice(0, 16) : [];
    const collocations = Array.isArray(obj?.collocations) ? obj.collocations.filter(Boolean).map(String).slice(0, 20) : [];
    return {
      word,
      parts_of_speech: partsOfSpeech,
      meanings_en: meaningsEn,
      meanings_zh: meaningsZh,
      // legacy field name (English only)
      meanings: meaningsEn,
      inflections,
      collocations
    };
  }

  async function queryWordDetailsEnglish(word) {
    const cleaned = normalizeWordQueryText(word);
    if (!cleaned) throw new Error('Empty word');
    if (!config?.queryApiEndpoint || !config?.queryModelName) {
      throw new Error('Query API is not configured');
    }

    const zhVariant = String(config?.nativeLanguage || 'zh-CN').toLowerCase().includes('zh-tw')
      ? 'Traditional Chinese'
      : 'Simplified Chinese';

    const prompt = `You are a bilingual English-Chinese dictionary assistant.

Given the word/phrase: ${JSON.stringify(cleaned)}

Return ONLY valid JSON (no Markdown, no code fences) with this schema:
{
  "word": string,
  "parts_of_speech": string[],
  "meanings_en": [{"pos": string, "definitions": string[]}],
  "meanings_zh": [{"pos": string, "definitions": string[]}],
  "inflections": string[],
  "collocations": string[]
}

Requirements:
- Definitions must be in English, concise.
- Chinese definitions must be in ${zhVariant}, concise.
- Include common inflections/variants when applicable (e.g., plural, past, past participle, -ing, 3rd person singular, comparative/superlative).
- Include common collocations/phrases (4-6 items).
- Do NOT include example sentences.`;

    const apiResponse = await callApiViaBackgroundWith(config.queryApiEndpoint, config.queryApiKey, {
      model: config.queryModelName,
      messages: [
        { role: 'system', content: 'Return only valid JSON.' },
        { role: 'user', content: prompt }
      ],
      temperature: 0.1,
      max_tokens: 900
    }, { queue: 'query' });

    const content = extractAssistantText(apiResponse);
    const parsed = tryParseJsonObject(content);
    if (!parsed) {
      throw new Error('Invalid JSON response');
    }

    return normalizeWordQueryResult(parsed, cleaned);
  }

  function createEmptyWordQueryResult(word) {
    const empty = {
      word: normalizeWordQueryText(word),
      parts_of_speech: [],
      meanings_en: [],
      meanings_zh: [],
      inflections: [],
      collocations: []
    };
    // legacy field name (English only)
    empty.meanings = empty.meanings_en;
    return empty;
  }

  function pushUnique(arr, value, maxLen = 50) {
    const v = String(value || '').trim();
    if (!v) return;
    if (arr.includes(v)) return;
    arr.push(v);
    if (arr.length > maxLen) arr.splice(0, arr.length - maxLen);
  }

  function getOrCreateMeaningBucket(result, pos, lang = 'en') {
    const p = String(pos || '').trim();
    if (!p) return null;
    const key = lang === 'zh' ? 'meanings_zh' : 'meanings_en';
    if (!Array.isArray(result[key])) result[key] = [];
    if (key === 'meanings_en') result.meanings = result[key]; // keep legacy alias updated

    let bucket = result[key].find(m => m.pos === p);
    if (!bucket) {
      bucket = { pos: p, definitions: [] };
      result[key].push(bucket);
    }
    return bucket;
  }

  function applyWordQueryNdjsonEvent(result, evt) {
    const type = String(evt?.type || '').trim();
    if (!type) return null;

    if (type === 'meta') {
      if (evt.word) result.word = normalizeWordQueryText(evt.word) || result.word;
      const parts = Array.isArray(evt.parts_of_speech) ? evt.parts_of_speech : [];
      parts.forEach(p => pushUnique(result.parts_of_speech, p, 16));
      return null;
    }

    if (type === 'pos') {
      pushUnique(result.parts_of_speech, evt.value, 16);
      return null;
    }

    if (type === 'meaning') {
      const lang = String(evt.lang || evt.language || '').trim().toLowerCase() === 'zh' ? 'zh' : 'en';
      const bucket = getOrCreateMeaningBucket(result, evt.pos, lang);
      if (!bucket) return null;
      pushUnique(bucket.definitions, evt.definition, 12);
      return null;
    }

    if (type === 'inflection') {
      pushUnique(result.inflections, evt.value, 24);
      return null;
    }

    if (type === 'collocation') {
      pushUnique(result.collocations, evt.value, 24);
      return null;
    }

    if (type === 'final' && evt.data && typeof evt.data === 'object') {
      return normalizeWordQueryResult(evt.data, result.word);
    }

    return null;
  }

  function queryWordDetailsEnglishStream(word, { onPartialData, onRawText } = {}) {
    const cleaned = normalizeWordQueryText(word);
    if (!cleaned) return { promise: Promise.reject(new Error('Empty word')), cancel: () => {} };
    if (!config?.queryApiEndpoint || !config?.queryModelName) {
      return { promise: Promise.reject(new Error('Query API is not configured')), cancel: () => {} };
    }

    const zhVariant = String(config?.nativeLanguage || 'zh-CN').toLowerCase().includes('zh-tw')
      ? 'Traditional Chinese'
      : 'Simplified Chinese';

    const prompt = `You are a bilingual English-Chinese dictionary assistant.

Given the word/phrase: ${JSON.stringify(cleaned)}

Stream output as NDJSON (one JSON object per line, no Markdown, no code fences).
Event types (examples):
- {"type":"meta","word":"...","parts_of_speech":["noun","verb"]}
- {"type":"meaning","lang":"en","pos":"noun","definition":"..."}
- {"type":"meaning","lang":"zh","pos":"noun","definition":"..."}
- {"type":"inflection","value":"..."}
- {"type":"collocation","value":"..."}
- {"type":"final","data":{...full schema below...}}

The final schema in the final event must be:
{"word":string,"parts_of_speech":string[],"meanings_en":[{"pos":string,"definitions":string[]}],"meanings_zh":[{"pos":string,"definitions":string[]}],"inflections":string[],"collocations":string[]}

Requirements:
- Definitions must be in English, concise.
- Chinese definitions must be in ${zhVariant}, concise.
- Include common inflections/variants when applicable.
- Include common collocations/phrases (4-6 items).
- Do NOT include example sentences.`;

    const result = createEmptyWordQueryResult(cleaned);
    let ndjsonBuffer = '';
    let finalData = null;
    let emittedAt = 0;
    let parsedAny = false;

    const stream = apiRequestStreamViaBackground(config.queryApiEndpoint, config.queryApiKey, {
      model: config.queryModelName,
      messages: [
        { role: 'system', content: 'Output NDJSON events only. End with a final event.' },
        { role: 'user', content: prompt }
      ],
      temperature: 0.1,
      max_tokens: 900,
      stream: true
    }, {
      onDelta: (delta, fullText) => {
        if (typeof onRawText === 'function' && !parsedAny) {
          try { onRawText(fullText); } catch {}
        }

        ndjsonBuffer += delta;
        const lines = ndjsonBuffer.split(/\r?\n/);
        ndjsonBuffer = lines.pop() || '';

        for (const rawLine of lines) {
          const line = String(rawLine || '').trim();
          if (!line) continue;
          let evt = null;
          try { evt = JSON.parse(line); } catch { evt = null; }
          if (!evt || typeof evt !== 'object') continue;
          parsedAny = true;
          const maybeFinal = applyWordQueryNdjsonEvent(result, evt);
          if (maybeFinal) finalData = maybeFinal;
        }

        if (typeof onPartialData === 'function' && parsedAny) {
          const now = Date.now();
          if (now - emittedAt >= 120) {
            emittedAt = now;
            try { onPartialData(result); } catch {}
          }
        }
      }
    });

    const promise = stream.promise.then((text) => {
      // flush buffer
      const rest = String(ndjsonBuffer || '').trim();
      if (rest) {
        const restLines = rest.split(/\r?\n/);
        for (const rawLine of restLines) {
          const line = String(rawLine || '').trim();
          if (!line) continue;
          let evt = null;
          try { evt = JSON.parse(line); } catch { evt = null; }
          if (!evt || typeof evt !== 'object') continue;
          parsedAny = true;
          const maybeFinal = applyWordQueryNdjsonEvent(result, evt);
          if (maybeFinal) finalData = maybeFinal;
        }
      }

      if (finalData) return finalData;

      // Fallback: model may ignore NDJSON and just output a JSON object at the end
      const parsed = tryParseJsonObject(text);
      if (parsed) return normalizeWordQueryResult(parsed, cleaned);

      if (parsedAny) return normalizeWordQueryResult(result, cleaned);
      throw new Error('Invalid stream response');
    });

    return { promise, cancel: stream.cancel };
  }

  function prefetchWordQuery(word) {
    // Backward compatible wrapper: do a query request and cache result (no UI updates)
    return prefetchWordQueryStreaming(word, {}).promise;
  }

  function prefetchWordQueryStreaming(word, { onPartialData, onRawText, onDone, onError } = {}) {
    if (!config?.enableWordQuery) return { promise: Promise.resolve(null), cancel: () => {} };
    const key = makeWordQueryCacheKey(word);
    if (!key) return { promise: Promise.resolve(null), cancel: () => {} };

    const cached = wordQueryCache.get(key);
    if (cached?.data) {
      wordQueryCache.delete(key);
      wordQueryCache.set(key, cached);
      return { promise: Promise.resolve(cached.data), cancel: () => {} };
    }

    const existing = wordQueryInFlight.get(key);
    if (existing?.promise) {
      const now = Date.now();
      const lastProgressAt = existing.state?.lastProgressAt || existing.state?.startedAt || 0;
      // If an in-flight request has no progress for a long time, treat it as stuck and restart.
      if (lastProgressAt && (now - lastProgressAt) > 20_000) {
        try { existing.cancel?.(); } catch {}
        wordQueryInFlight.delete(key);
        // restart fresh
        return prefetchWordQueryStreaming(word, { onPartialData, onRawText, onDone, onError });
      }
      if (onPartialData || onRawText || onDone || onError) {
        existing.listeners.add({ onPartialData, onRawText, onDone, onError });
        if (existing.state?.hasStructured && typeof onPartialData === 'function') {
          try { onPartialData(existing.state.partial); } catch {}
        } else if (existing.state?.rawText && typeof onRawText === 'function') {
          try { onRawText(existing.state.rawText); } catch {}
        }
      }
      return { promise: existing.promise, cancel: existing.cancel || (() => {}) };
    }

    const entry = {
      listeners: new Set(),
      state: {
        rawText: '',
        partial: createEmptyWordQueryResult(word),
        hasStructured: false,
        startedAt: Date.now(),
        lastProgressAt: Date.now()
      }
    };

    if (onPartialData || onRawText || onDone || onError) {
      entry.listeners.add({ onPartialData, onRawText, onDone, onError });
    }

    const stream = queryWordDetailsEnglishStream(word, {
      onPartialData: (partial) => {
        entry.state.partial = partial;
        entry.state.hasStructured = true;
        entry.state.lastProgressAt = Date.now();
        notifyWordQueryListeners(entry, 'partial', partial);
      },
      onRawText: (text) => {
        entry.state.rawText = text;
        entry.state.lastProgressAt = Date.now();
        if (!entry.state.hasStructured) notifyWordQueryListeners(entry, 'raw', text);
      }
    });

    entry.cancel = () => {
      try { stream.cancel?.(); } catch {}
    };

    entry.promise = stream.promise.then((data) => {
      upsertWordQueryCacheItem(key, data);
      scheduleSaveWordQueryCache();
      notifyWordQueryListeners(entry, 'done', data);
      return data;
    }).catch((err) => {
      notifyWordQueryListeners(entry, 'error', err);
      throw err;
    }).finally(() => {
      wordQueryInFlight.delete(key);
    });

    wordQueryInFlight.set(key, entry);
    return { promise: entry.promise, cancel: entry.cancel };
  }

  function forceRetryWordQuery(word) {
    const cleaned = normalizeWordQueryText(word);
    const key = makeWordQueryCacheKey(cleaned);
    if (!key) return;

    // Cancel any active stream for this key
    if (activeWordQueryStream?.key === key) {
      try { activeWordQueryStream.cancel?.(); } catch {}
      activeWordQueryStream = null;
    }

    // cancel & clear any in-flight entry for this key
    const existing = wordQueryInFlight.get(key);
    if (existing?.cancel) {
      try { existing.cancel(); } catch {}
    }
    wordQueryInFlight.delete(key);
    wordQueryCache.delete(key);
    scheduleSaveWordQueryCache(100);

    if (!tooltip || tooltip.style.display !== 'block') return;
    if (tooltip.dataset.wordQueryKey !== key) return;

    const container = tooltip.querySelector('.vocabmeld-tooltip-query');
    if (container) container.innerHTML = buildTooltipQueryHtmlLoading();

    let hasStructuredUpdate = false;
    const stream = prefetchWordQueryStreaming(cleaned, {
      onPartialData: (partial) => {
        hasStructuredUpdate = true;
        if (!tooltip || tooltip.style.display !== 'block') return;
        if (tooltip.dataset.wordQueryKey !== key) return;
        const liveContainer = tooltip.querySelector('.vocabmeld-tooltip-query');
        if (!liveContainer) return;
        liveContainer.innerHTML = buildTooltipQueryHtmlData(partial, { statusText: '生成中…', isPartial: true });
      },
      onRawText: (text) => {
        if (hasStructuredUpdate) return;
        if (!tooltip || tooltip.style.display !== 'block') return;
        if (tooltip.dataset.wordQueryKey !== key) return;
        const liveContainer = tooltip.querySelector('.vocabmeld-tooltip-query');
        if (!liveContainer) return;
        liveContainer.innerHTML = buildTooltipQueryHtmlStreaming(text);
      }
    });

    activeWordQueryStream = { key, cancel: stream.cancel };

    stream.promise.then((data) => {
      if (!tooltip || tooltip.style.display !== 'block') return;
      if (tooltip.dataset.wordQueryKey !== key) return;
      const finalContainer = tooltip.querySelector('.vocabmeld-tooltip-query');
      if (finalContainer) finalContainer.innerHTML = buildTooltipQueryHtmlData(data);
    }).catch((err) => {
      if (!tooltip || tooltip.style.display !== 'block') return;
      if (tooltip.dataset.wordQueryKey !== key) return;
      const errorContainer = tooltip.querySelector('.vocabmeld-tooltip-query');
      if (errorContainer) errorContainer.innerHTML = buildTooltipQueryHtmlError(err?.message || String(err));
    });
  }

  async function translateParagraphToTarget(text, sourceLang, targetLang) {
    const limited = (text || '').slice(0, MAX_INLINE_TRANSLATION_CHARS);
    const prompt = `请将下面的文本从 ${sourceLang} 翻译为 ${targetLang}（学习语言）。\n\n要求：\n- 保持原意、自然流畅\n- 不要添加解释、不要总结\n- 只输出翻译后的文本\n\n文本：\n${limited}`;

    const apiResponse = await callApiViaBackground({
      model: config.modelName,
      messages: [
        { role: 'system', content: '你是一个专业翻译助手。只输出用户要求的内容。' },
        { role: 'user', content: prompt }
      ],
      temperature: 0.2,
      max_tokens: 1200
    });

    return extractAssistantText(apiResponse);
  }

  async function translateSentencesToTarget(sentences, sourceLang, targetLang) {
    const input = sentences.map(s => s.text);
    const prompt = `请把下面的句子数组从 ${sourceLang} 翻译为 ${targetLang}（学习语言）。\n\n要求：\n- 输出必须是 JSON 数组，长度与输入一致\n- 每个元素是对应句子的翻译字符串\n- 不要输出任何多余内容\n\n输入：\n${JSON.stringify(input)}`;

    const apiResponse = await callApiViaBackground({
      model: config.modelName,
      messages: [
        { role: 'system', content: '你是一个专业翻译助手。始终返回有效的 JSON。' },
        { role: 'user', content: prompt }
      ],
      temperature: 0.2,
      max_tokens: 1200
    });

    const content = extractAssistantText(apiResponse) || '[]';
    let parsed = [];
    try {
      parsed = JSON.parse(content);
      if (!Array.isArray(parsed)) parsed = [];
    } catch {
      const jsonMatch = content.match(/\[[\s\S]*\]/);
      if (jsonMatch) {
        parsed = JSON.parse(jsonMatch[0]);
      }
      if (!Array.isArray(parsed)) parsed = [];
    }

    return parsed.map(x => (typeof x === 'string' ? x : '')).slice(0, sentences.length);
  }

  function integrateParagraphTranslation(element, translationText) {
    if (element.hasAttribute('data-vocabmeld-paragraph-translated')) return false;

    const originalFragment = document.createDocumentFragment();
    while (element.firstChild) {
      originalFragment.appendChild(element.firstChild);
    }

    const translatedSpan = document.createElement('span');
    translatedSpan.className = 'vocabmeld-paragraph-translated';
    translatedSpan.textContent = translationText;

    const originalWrapper = document.createElement('span');
    originalWrapper.className = 'vocabmeld-paragraph-original';

    const originalContent = document.createElement('span');
    originalContent.className = 'vocabmeld-paragraph-original-content';
    originalContent.appendChild(originalFragment);

    originalWrapper.appendChild(document.createTextNode('('));
    originalWrapper.appendChild(originalContent);
    originalWrapper.appendChild(document.createTextNode(')'));

    element.appendChild(translatedSpan);
    element.appendChild(document.createTextNode(' '));
    element.appendChild(originalWrapper);

    element.setAttribute('data-vocabmeld-paragraph-translated', 'true');
    element.setAttribute('data-vocabmeld-processed', 'true');
    return true;
  }

  function wrapRangeWithTranslation(range, translationText) {
    const extracted = range.extractContents();

    const wrapper = document.createElement('span');
    wrapper.className = 'vocabmeld-segment-translated';

    const translatedSpan = document.createElement('span');
    translatedSpan.className = 'vocabmeld-segment-translation';
    translatedSpan.textContent = translationText;

    const originalWrapper = document.createElement('span');
    originalWrapper.className = 'vocabmeld-segment-original';

    const originalContent = document.createElement('span');
    originalContent.className = 'vocabmeld-segment-original-content';
    originalContent.appendChild(extracted);

    originalWrapper.appendChild(document.createTextNode('('));
    originalWrapper.appendChild(originalContent);
    originalWrapper.appendChild(document.createTextNode(')'));

    wrapper.appendChild(translatedSpan);
    wrapper.appendChild(document.createTextNode(' '));
    wrapper.appendChild(originalWrapper);

    range.insertNode(wrapper);
    return true;
  }

  async function maybeIntegrateParagraphTranslation(element, text, fingerprint) {
    if (!config?.enabled) return;
    if (!config.apiEndpoint) return;
    if ((config.paragraphTranslationRate ?? 0) <= 0) return;
    if (!isEligibleForInlineTranslation(element)) return;
    if (element.hasAttribute('data-vocabmeld-paragraph-translated')) return;
    if (config.processMode === 'target-only') return;

    const r = stableUnitRandom(`${fingerprint}:paragraph`);
    if (r >= (config.paragraphTranslationRate / 100)) return;

    const detectedLang = detectLanguage(text);
    if (!isNativeLanguage(detectedLang, config.nativeLanguage)) return;

    const translated = await translateParagraphToTarget(text, config.nativeLanguage, config.targetLanguage);
    if (!translated) return;

    return integrateParagraphTranslation(element, translated);
  }

  async function maybeIntegrateSentenceTranslations(element, fingerprint) {
    if (!config?.enabled) return;
    if (!config.apiEndpoint) return;
    if ((config.sentenceTranslationRate ?? 0) <= 0) return;
    if (!isEligibleForInlineTranslation(element)) return;
    if (element.hasAttribute('data-vocabmeld-paragraph-translated')) return;
    if (config.processMode === 'target-only') return;

    const r = stableUnitRandom(`${fingerprint}:sentenceBlock`);
    if (r >= (config.sentenceTranslationRate / 100)) return;

    const textNodes = getReplaceableTextNodes(element);
    if (!textNodes.length) return;

    const { fullText, index } = buildTextIndex(textNodes, MAX_INLINE_TRANSLATION_CHARS);
    if (!fullText.trim()) return;

    const detectedLang = detectLanguage(fullText);
    if (!isNativeLanguage(detectedLang, config.nativeLanguage)) return;

    const picked = pickSentencesForTranslation(fullText, fingerprint);
    if (!picked.length) return;

    const translations = await translateSentencesToTarget(picked, config.nativeLanguage, config.targetLanguage);
    if (!translations.length) return;

    // 从后往前替换，降低 Range 失效概率
    const pairs = picked
      .map((p, i) => ({ ...p, translation: (translations[i] || '').trim() }))
      .filter(p => p.translation)
      .sort((a, b) => b.start - a.start);

    let changed = false;
    for (const p of pairs) {
      const startPoint = getDomPointAtIndex(index, p.start);
      const endPoint = getDomPointAtIndex(index, p.end);
      if (!startPoint || !endPoint) continue;

      try {
        const range = document.createRange();
        range.setStart(startPoint.node, startPoint.offset);
        range.setEnd(endPoint.node, endPoint.offset);
        const extractedText = range.toString().trim();
        if (!extractedText) continue;

        wrapRangeWithTranslation(range, p.translation);
        changed = true;
      } catch (e) {
        console.error('[VocabMeld] Sentence integration error:', e);
      }
    }

    if (changed) {
      element.setAttribute('data-vocabmeld-processed', 'true');
    }
    return changed;
  }

  // ============ API 调用 ============
  async function translateText(text, options = {}) {
    if (!config.apiEndpoint) {
      throw new Error('API 未配置');
    }

    // 确保缓存已加载
    if (wordCache.size === 0) {
      await loadWordCache();
    }

    const detectedLang = detectLanguage(text);
    const isNative = isNativeLanguage(detectedLang, config.nativeLanguage);
    
    // 根据处理模式检查是否需要处理该文本
    // native-only: 只处理母语网页（将母语翻译为目标语言）
    // target-only: 只处理目标语言网页（将目标语言翻译为母语）
    // both: 两者均处理
    if (config.processMode === 'native-only' && !isNative) {
      return { immediate: [], async: null };
    }
    if (config.processMode === 'target-only' && isNative) {
      return { immediate: [], async: null };
    }
    
    const sourceLang = isNative ? config.nativeLanguage : detectedLang;
    const targetLang = isNative ? config.targetLanguage : config.nativeLanguage;
    const baseMaxReplacements = INTENSITY_CONFIG[config.intensity]?.maxPerParagraph || 8;
    const maxReplacementsOverride = Number.isFinite(options.maxReplacementsOverride)
      ? Math.max(1, Math.floor(options.maxReplacementsOverride))
      : baseMaxReplacements;
    const maxReplacementsCap = Number.isFinite(options.maxReplacementsCap) ? options.maxReplacementsCap : Infinity;
    const maxReplacements = Math.max(1, Math.min(maxReplacementsOverride, maxReplacementsCap));

    // 检查缓存 - 只检查有意义的词汇（排除常见停用词）
    const words = (text.match(/\b[a-zA-Z]{5,}\b/g) || []).filter(w => !STOP_WORDS.has(w.toLowerCase()));
    
    // 对于中文，提取有意义的短语（2-4个字符）
    // 注意：这里只提取用于缓存检查，实际翻译由AI决定返回哪些词汇
    // 提取2-4个字符的短语（避免提取过多无意义的片段）
    const chinesePhrases = [];
    const chineseText = text.match(/[\u4e00-\u9fff]+/g) || [];
    
    // 从中文文本中提取2-4个字符的短语（滑动窗口，步长为1）
    for (const phrase of chineseText) {
      if (phrase.length >= 2) {
        // 提取2-4个字符的短语
        for (let len = 2; len <= Math.min(4, phrase.length); len++) {
          for (let i = 0; i <= phrase.length - len; i++) {
            const subPhrase = phrase.substring(i, i + len);
            chinesePhrases.push(subPhrase);
          }
        }
      }
    }
    
    const allWords = [...new Set([...words, ...chinesePhrases])];

    const cached = [];
    const uncached = [];
    const cachedWordsSet = new Set(); // 用于去重

    for (const word of allWords) {
      const key = `${word.toLowerCase()}:${sourceLang}:${targetLang}`;
      if (wordCache.has(key)) {
        const lowerWord = word.toLowerCase();
        if (!cachedWordsSet.has(lowerWord)) {
          cached.push({ word, ...wordCache.get(key) });
          cachedWordsSet.add(lowerWord);
        }
      } else {
        uncached.push(word);
      }
    }
    
    // 额外检查：检查文本中是否包含已缓存的中文词汇（用于处理AI返回的词汇与提取不一致的情况）
    const lowerText = text.toLowerCase();
    const langPairKey = `${sourceLang}:${targetLang}`;
    const cjkCandidates = cachedCjkWordsByLangPair.get(langPairKey);
    if (cjkCandidates && cjkCandidates.size > 0 && /[\u4e00-\u9fff]/.test(text)) {
      for (const lowerCachedWord of cjkCandidates) {
        if (cachedWordsSet.has(lowerCachedWord)) continue;
        if (!lowerText.includes(lowerCachedWord)) continue;

        const cacheKey = makeCacheKey(lowerCachedWord, sourceLang, targetLang);
        const value = wordCache.get(cacheKey);
        if (!value) continue;

        const idx = lowerText.indexOf(lowerCachedWord);
        if (idx >= 0) {
          cached.push({
            word: text.substring(idx, idx + lowerCachedWord.length),
            ...value
          });
          cachedWordsSet.add(lowerCachedWord);
        }
      }
    }

    // 获取已学会单词列表
    const learnedWordsSet = new Set((config.learnedWords || []).map(w => w.original.toLowerCase()));
    
    // 过滤缓存结果（按难度，排除已学会单词）
    const filteredCached = cached
      .filter(c => 
        isDifficultyCompatible(c.difficulty || 'B1', config.difficultyLevel) &&
        !learnedWordsSet.has(c.word.toLowerCase())
      )
      .map(c => {
        const idx = text.toLowerCase().indexOf(c.word.toLowerCase());
        return { 
          original: c.word, 
          translation: c.translation, 
          phonetic: c.phonetic, 
          difficulty: c.difficulty, 
          position: idx >= 0 ? idx : 0, 
          fromCache: true 
        };
      });

    // 立即返回缓存结果（立即显示）
    const immediateResults = filteredCached.slice(0, maxReplacements);
    
    // 更新统计
    if (immediateResults.length > 0) {
      updateStats({ cacheHits: immediateResults.length, cacheMisses: 0 });
    }

    // 如果没有未缓存的词汇，直接返回缓存结果
    if (uncached.length === 0) {
      return { immediate: immediateResults, async: null };
    }

    // 构建只包含未缓存词汇的文本用于发送给 AI
    const filteredText = reconstructTextWithWords(text, uncached);

    // 判断是否需要限制异步替换数量
    const cacheSatisfied = immediateResults.length >= maxReplacements;
    const minTextLenForApi = Number.isFinite(options.minTextLenForApi) ? options.minTextLenForApi : 50;
    const textTooShort = filteredText.trim().length < minTextLenForApi;
    
    // 如果文本太短，不需要调用API
    if (textTooShort) {
      return { immediate: immediateResults, async: null };
    }

    // 计算还需要翻译的词汇数量
    const remainingSlots = maxReplacements - immediateResults.length;
    
    // 如果缓存已满足配置，异步替换最多1个词；否则按剩余槽位计算
    const maxAsyncReplacements = cacheSatisfied ? 1 : remainingSlots;
    
    // 如果不需要异步替换，直接返回
    if (maxAsyncReplacements <= 0) {
      return { immediate: immediateResults, async: null };
    }
    
    // 动态计算AI应该返回的词汇数量（通常是配置值的1.5-2倍，让AI有选择空间）
    // 但如果缓存已满足或文本极少，限制AI返回数量
    const aiTargetCount = cacheSatisfied 
      ? 1 
      : Math.max(maxAsyncReplacements, Math.ceil(maxReplacements * 1.5));

    // 异步调用 API，处理未缓存的词汇（不阻塞立即返回）
    const asyncPromise = (async () => {
      try {
        const prompt = `你是一个语言学习助手。请分析以下文本，选择适合学习的词汇进行翻译。

## 规则：
1. 选择约 ${aiTargetCount} 个词汇（实际返回数量可以根据文本内容灵活调整，但不要超过 ${maxReplacements * 2} 个）
2. 不要翻译：域名、地址、缩写、人名、地名、产品名、数字、代码、URL、已经是目标语言的词
3. 优先选择：有学习价值的词汇、不同难度级别的词汇
4. 翻译方向：从 ${sourceLang} 翻译到 ${targetLang}
5. 翻译倾向：结合上下文，夹杂起来也能容易被理解，尽量只翻译成最合适的词汇，而不是多个含义。

## CEFR等级从简单到复杂依次为：A1-C2

## 输出格式：
返回 JSON 数组，每个元素包含：
- original: 原词
- translation: 翻译结果
- phonetic: 学习语言(${config.targetLanguage})的音标/发音
- difficulty: CEFR 难度等级 (A1/A2/B1/B2/C1/C2)，请谨慎评估

## 文本：
${filteredText}

## 输出：
只返回 JSON 数组，不要其他内容。`;

        const apiResponse = await new Promise((resolve, reject) => {
          chrome.runtime.sendMessage({
            action: 'apiRequest',
            endpoint: config.apiEndpoint,
            apiKey: config.apiKey,
            body: {
              model: config.modelName,
              messages: [
                { role: 'system', content: '你是一个专业的语言学习助手。始终返回有效的 JSON 格式。' },
                { role: 'user', content: prompt }
              ],
              temperature: 0.3,
              max_tokens: 2000
            }
          }, response => {
            if (chrome.runtime.lastError) {
              reject(new Error(chrome.runtime.lastError.message));
            } else if (!response?.success) {
              reject(new Error(response?.error || 'API request failed'));
            } else {
              resolve(response.data);
            }
          });
        });

        const data = apiResponse;
        const content = data.choices?.[0]?.message?.content || '[]';
        
        let allResults = [];
        try {
          allResults = JSON.parse(content);
          if (!Array.isArray(allResults)) {
            const jsonMatch = content.match(/\[[\s\S]*\]/);
            if (jsonMatch) allResults = JSON.parse(jsonMatch[0]);
          }
        } catch (e) {
          const jsonMatch = content.match(/\[[\s\S]*\]/);
          if (jsonMatch) allResults = JSON.parse(jsonMatch[0]);
        }

        // 先缓存所有词汇（包括所有难度级别），供不同难度设置的用户使用
        // 过滤掉2字以下的中文词汇和小于5个字符的英文单词（避免简单词影响语境）
        for (const item of allResults) {
          // 对于中文，不存储1个字的内容（即只存储2个字及以上的词汇）
          const isChinese = /[\u4e00-\u9fff]/.test(item.original);
          if (isChinese && item.original.length < 2) {
            continue; // 跳过1个字的中文词汇（只存储2个字及以上的）
          }
          // 对于英文，不存储小于5个字符的单词
          const isEnglish = /^[a-zA-Z]+$/.test(item.original);
          if (isEnglish && item.original.length < 5) {
            continue; // 跳过小于5个字符的英文单词
          }
          
          upsertWordCacheItem(item, sourceLang, targetLang);
        }
        // 确保缓存保存完成
        await saveWordCache();

        // 本地过滤：只保留符合用户难度设置的词汇，并过滤掉小于5个字符的英文单词
        const filteredResults = allResults.filter(item => {
          // 过滤难度级别
          if (!isDifficultyCompatible(item.difficulty || 'B1', config.difficultyLevel)) {
            return false;
          }
          // 过滤小于5个字符的英文单词
          const isEnglish = /^[a-zA-Z]+$/.test(item.original);
          if (isEnglish && item.original.length < 5) {
            return false;
          }
          return true;
        });

        // 更新统计
        updateStats({ newWords: filteredResults.length, cacheHits: cached.length, cacheMisses: 1 });

        // 修正 AI 返回结果的位置（从过滤文本映射回原始文本）
        const correctedResults = filteredResults.map(result => {
          const originalIndex = text.toLowerCase().indexOf(result.original.toLowerCase());
          return {
            ...result,
            position: originalIndex >= 0 ? originalIndex : (Number.isFinite(result.position) ? result.position : 0)
          };
        });

        // 合并缓存结果（去重，避免与已显示的缓存结果重复，排除已学会单词）
        const immediateWords = new Set(immediateResults.map(r => r.original.toLowerCase()));
        const currentLearnedWords = new Set((config.learnedWords || []).map(w => w.original.toLowerCase()));
        const cachedResults = cached
          .filter(c => 
            !immediateWords.has(c.word.toLowerCase()) && 
            !correctedResults.some(r => r.original.toLowerCase() === c.word.toLowerCase()) &&
            !currentLearnedWords.has(c.word.toLowerCase()) &&
            isDifficultyCompatible(c.difficulty || 'B1', config.difficultyLevel)
          )
          .map(c => {
            const idx = text.toLowerCase().indexOf(c.word.toLowerCase());
            return { original: c.word, translation: c.translation, phonetic: c.phonetic, difficulty: c.difficulty, position: idx, fromCache: true };
          });
        
        // API 结果也要过滤已学会单词
        const filteredCorrectedResults = correctedResults.filter(r => !currentLearnedWords.has(r.original.toLowerCase()));

        // 合并结果：补充的缓存结果 + API结果
        // 限制异步替换数量（如果缓存已满足配置或文本极少，最多只替换1个词）
        const mergedResults = [...cachedResults, ...filteredCorrectedResults];
        return mergedResults.slice(0, maxAsyncReplacements);

      } catch (error) {
        console.error('[VocabMeld] Async API Error:', error);
        // API失败时返回空数组，不影响已显示的缓存结果
        return [];
      }
    })();

    return { immediate: immediateResults, async: asyncPromise };
  }

  // ============ 特定单词处理 ============
  async function translateSpecificWords(targetWords) {
    if (!config.apiEndpoint || !targetWords?.length) {
      return [];
    }

    const detectedLang = detectLanguage(targetWords.join(' '));
    const isNative = isNativeLanguage(detectedLang, config.nativeLanguage);
    const sourceLang = isNative ? config.nativeLanguage : detectedLang;
    const targetLang = isNative ? config.targetLanguage : config.nativeLanguage;

    const uncached = [];
    const cached = [];

    // 检查缓存（复用统一流程）
    for (const word of targetWords) {
      const key = `${word.toLowerCase()}:${sourceLang}:${targetLang}`;
      if (wordCache.has(key)) {
        // LRU: 访问时移到末尾（通过删除再添加实现）
        const cachedItem = wordCache.get(key);
        wordCache.delete(key);
        wordCache.set(key, cachedItem);
        cached.push({ word, ...cachedItem });
      } else {
        uncached.push(word);
      }
    }

    let allResults = cached.map(c => ({
      original: c.word,
      translation: c.translation,
      phonetic: c.phonetic,
      difficulty: c.difficulty
    }));

    // 如果有未缓存的单词，调用API
    if (uncached.length > 0) {
      try {
        const prompt = `你是一个语言学习助手。请翻译以下特定词汇。

## 规则：
1. 必须翻译所有提供的词汇，不要跳过任何词
2. 如果单词是${sourceLang}，则翻译到${targetLang}，反之亦然

## CEFR等级从简单到复杂依次为：A1-C2

## 输出格式：
返回 JSON 数组，每个元素包含：
- original: 原词
- translation: 翻译结果
- phonetic: 学习语言(${config.targetLanguage})的音标/发音
- difficulty: CEFR 难度等级 (A1/A2/B1/B2/C1/C2)

## 要翻译的词汇：
${uncached.join(', ')}

## 输出：
只返回 JSON 数组，不要其他内容。`;

        const apiResponse = await new Promise((resolve, reject) => {
          chrome.runtime.sendMessage({
            action: 'apiRequest',
            endpoint: config.apiEndpoint,
            apiKey: config.apiKey,
            body: {
              model: config.modelName,
              messages: [
                { role: 'system', content: '你是一个专业的语言学习助手。始终返回有效的 JSON 格式。' },
                { role: 'user', content: prompt }
              ],
              temperature: 0.3,
              max_tokens: 1000
            }
          }, response => {
            if (chrome.runtime.lastError) {
              reject(new Error(chrome.runtime.lastError.message));
            } else if (!response?.success) {
              reject(new Error(response?.error || 'API request failed'));
            } else {
              resolve(response.data);
            }
          });
        });

        const data = apiResponse;
        const content = data.choices?.[0]?.message?.content || '[]';

        let apiResults = [];
        try {
          apiResults = JSON.parse(content);
          if (!Array.isArray(apiResults)) {
            const jsonMatch = content.match(/\[[\s\S]*\]/);
            if (jsonMatch) apiResults = JSON.parse(jsonMatch[0]);
          }
        } catch (e) {
          const jsonMatch = content.match(/\[[\s\S]*\]/);
          if (jsonMatch) apiResults = JSON.parse(jsonMatch[0]);
        }

        // 缓存结果（复用统一流程，实现LRU淘汰）
        // 过滤掉2字以下的中文词汇和小于5个字符的英文单词（避免简单词影响语境）
        for (const item of apiResults) {
          // 对于中文，不存储1个字的内容（即只存储2个字及以上的词汇）
          const isChinese = /[\u4e00-\u9fff]/.test(item.original);
          if (isChinese && item.original.length < 2) {
            continue; // 跳过1个字的中文词汇（只存储2个字及以上的）
          }
          // 对于英文，不存储小于5个字符的单词
          const isEnglish = /^[a-zA-Z]+$/.test(item.original);
          if (isEnglish && item.original.length < 5) {
            continue; // 跳过小于5个字符的英文单词
          }
          
          upsertWordCacheItem(item, sourceLang, targetLang);
        }
        // 确保缓存保存完成
        await saveWordCache();

        allResults = [...allResults, ...apiResults];

        // 更新统计
        updateStats({ newWords: apiResults.length, cacheHits: cached.length, cacheMisses: 1 });

      } catch (error) {
        console.error('[VocabMeld] API Error for specific words:', error);
        // 如果API失败，至少返回缓存的结果
      }
    }

    return allResults.filter(item => targetWords.some(w => w.toLowerCase() === item.original.toLowerCase()));
  }

  async function processSpecificWords(targetWords) {
    if (!config?.enabled || !targetWords?.length) {
      return 0;
    }
    if (!shouldProcessSite()) return 0;

    const targetWordSet = new Set(targetWords.map(w => w.toLowerCase()));
    let processed = 0;

    // 首先检查已翻译的元素，看是否有目标单词已经被翻译了
    const alreadyTranslated = [];
    document.querySelectorAll('.vocabmeld-translated').forEach(el => {
      const original = el.getAttribute('data-original');
      if (original && targetWordSet.has(original.toLowerCase())) {
        alreadyTranslated.push(original.toLowerCase());
      }
    });

    // 查找页面中包含目标单词的文本节点（包括已处理过的容器）
    const textNodes = [];
    const walker = document.createTreeWalker(document.body, NodeFilter.SHOW_TEXT, {
      acceptNode: (node) => {
        // 跳过不应该处理的节点类型
        const parent = node.parentElement;
        if (!parent) return NodeFilter.FILTER_REJECT;
        
        // 跳过脚本、样式等标签
        if (SKIP_TAGS.includes(parent.tagName)) return NodeFilter.FILTER_REJECT;
        
        // 跳过代码相关的类
        const classList = parent.className?.toString() || '';
        if (SKIP_CLASSES.some(cls => classList.includes(cls) && cls !== 'vocabmeld-translated')) {
          return NodeFilter.FILTER_REJECT;
        }
        
        // 跳过隐藏元素（使用 offsetParent 快速检测）
        if (parent.offsetParent === null && parent.tagName !== 'BODY' && parent.tagName !== 'HTML') {
          const position = parent.style.position;
          if (position !== 'fixed' && position !== 'sticky') {
            return NodeFilter.FILTER_REJECT;
          }
        }
        
        // 跳过可编辑元素
        if (parent.isContentEditable) return NodeFilter.FILTER_REJECT;
        
        const text = node.textContent.trim();
        if (text.length === 0) return NodeFilter.FILTER_REJECT;
        
        // 跳过代码文本
        if (isCodeText(text)) return NodeFilter.FILTER_REJECT;
        
        return NodeFilter.FILTER_ACCEPT;
      }
    });

    let node;
    while (node = walker.nextNode()) {
      const text = node.textContent;
      // 检查文本节点是否包含目标单词（作为完整单词）
      const words = text.match(/\b[a-zA-Z]{5,}\b/g) || [];
      const chineseWords = text.match(/[\u4e00-\u9fff]{2,4}/g) || [];
      const allWords = [...words, ...chineseWords];

      // 检查是否包含目标单词（且该单词还没有被翻译）
      const containsTarget = allWords.some(word => {
        const lowerWord = word.toLowerCase();
        return targetWordSet.has(lowerWord) && !alreadyTranslated.includes(lowerWord);
      });

      if (containsTarget) {
        textNodes.push(node);
      }
    }

    // 如果没有找到未翻译的文本节点，说明单词可能已经被翻译了
    if (textNodes.length === 0) {
      return 0;
    }

    // 构造包含目标单词的文本段落用于处理
    const segments = [];
    for (const textNode of textNodes) {
      // 获取更大的上下文（父元素的文本内容）
      const container = textNode.parentElement;
      if (!container) continue;
      
      // 获取容器的完整文本内容（包括已翻译的部分）
      const containerText = getTextContent(container);
      
      // 如果容器文本太短，尝试获取更大的上下文
      let contextText = containerText;
      if (contextText.length < 30) {
        const grandParent = container.parentElement;
        if (grandParent) {
          contextText = getTextContent(grandParent);
        }
      }

      if (contextText.length >= 10) {
        const path = getElementPath(container);
        const fingerprint = generateFingerprint(contextText, path);
        
        // 检查是否已经处理过这个段落
        const isProcessed = container.hasAttribute('data-vocabmeld-processed') || 
                           container.closest('[data-vocabmeld-processed]');
        
        segments.push({
          element: container,
          text: contextText,
          fingerprint: fingerprint,
          isProcessed: !!isProcessed
        });
      }
    }

    // 去重
    const uniqueSegments = segments.filter((segment, index, self) =>
      index === self.findIndex(s => s.fingerprint === segment.fingerprint)
    );

    // 获取目标单词的翻译
    const translations = await translateSpecificWords(targetWords);

    if (translations.length === 0) {
      return 0;
    }

    // 应用到每个段落
    for (const segment of uniqueSegments) {
      // 为每个翻译添加位置信息（基于当前段落的文本）
      const replacements = translations.map(translation => {
        const position = segment.text.toLowerCase().indexOf(translation.original.toLowerCase());
        return {
          original: translation.original,
          translation: translation.translation,
          phonetic: translation.phonetic,
          difficulty: translation.difficulty,
          position: position >= 0 ? position : 0
        };
      }).filter(r => r.position >= 0 || segment.text.toLowerCase().includes(r.original.toLowerCase()));

      if (replacements.length === 0) continue;

      const count = applyReplacements(segment.element, replacements);
      processed += count;
    }

    return processed;
  }

  // ============ 页面处理 ============
  const MAX_CONCURRENT = 3; // 最大并发请求数
  const MAX_SEGMENTS_PER_REQUEST = 5; // 合并段落：每个请求最多处理的段落数
  const REQUEST_INTERVAL_MS = 1000; // 合并段落：请求间隔（避免触发速率限制）
  const PROCESS_DELAY_MS = 50; // 批次间延迟，避免阻塞主线程

  // 使用 IntersectionObserver 实现懒加载
  function setupIntersectionObserver() {
    if (intersectionObserver) {
      intersectionObserver.disconnect();
    }
    observedContainers = new WeakSet();

    intersectionObserver = new IntersectionObserver((entries) => {
      if (document.hidden || !isTabActive) return;
      if (!shouldProcessSite()) return;
      let hasNewVisible = false;
      
      for (const entry of entries) {
        if (entry.isIntersecting) {
          const container = entry.target;
          // 跳过已处理的容器
          if (container.hasAttribute('data-vocabmeld-processed')) {
            continue;
          }
          // 跳过正在处理的容器
          if (container.hasAttribute(PROCESSING_ATTR)) {
            continue;
          }
          
          // 添加到待处理队列（即使已有 observing 标记，因为可能之前处理时被跳过了）
          if (!pendingContainers.has(container)) {
            pendingContainers.add(container);
            container.setAttribute('data-vocabmeld-observing', 'true');
            hasNewVisible = true;
          }
        }
      }

      // 有新可见容器时，触发处理
      if (hasNewVisible && !isProcessing) {
        processPendingContainers();
      }
    }, {
      rootMargin: `${VIEWPORT_PREFETCH_MARGIN_PX}px 0px`, // 提前加载视口上下文
      threshold: 0
    });
  }

  function getSegmentMaxReplacements(segment) {
    const base = INTENSITY_CONFIG[config?.intensity]?.maxPerParagraph || 8;
    const cap = Number.isFinite(segment?.maxReplacementsCap) ? segment.maxReplacementsCap : Infinity;
    return Math.max(1, Math.min(base, cap));
  }

  function pickSegmentReplacements(replacements, segment, whitelistWords, alreadyReplaced = null) {
    const textLower = String(segment?.text || '').toLowerCase();
    const selected = [];
    const seen = new Set();

    for (const r of replacements || []) {
      const original = String(r?.original || '').trim();
      if (!original) continue;
      const lower = original.toLowerCase();
      if (seen.has(lower)) continue;
      if (whitelistWords?.has(lower)) continue;
      if (alreadyReplaced?.has(lower)) continue;
      if (!textLower.includes(lower)) continue;
      seen.add(lower);
      const position = textLower.indexOf(lower);
      selected.push({
        ...r,
        original,
        position: position >= 0 ? position : 0
      });
      if (selected.length >= getSegmentMaxReplacements(segment)) break;
    }

    return selected;
  }

  async function processBatchSegments(batch, whitelistWords) {
    const segments = Array.isArray(batch) ? batch.filter(s => s?.element?.isConnected) : [];
    if (segments.length === 0) return;

    const activeSegments = [];
    for (const segment of segments) {
      if (segment.element.hasAttribute(PROCESSING_ATTR)) continue;
      segment.element.setAttribute(PROCESSING_ATTR, 'true');
      activeSegments.push(segment);
    }

    const finalize = (segment) => {
      try { segment.element.removeAttribute(PROCESSING_ATTR); } catch {}
      processedFingerprints.add(segment.fingerprint);
      try { segment.element.setAttribute(SCANNED_ATTR, segment.fingerprint); } catch {}
    };

    try {
      const candidates = [];
      for (const segment of activeSegments) {
        try {
          const paragraphApplied = await maybeIntegrateParagraphTranslation(segment.element, segment.text, segment.fingerprint);
          if (paragraphApplied) continue;
          const sentenceApplied = await maybeIntegrateSentenceTranslations(segment.element, segment.fingerprint);
          if (sentenceApplied) processedFingerprints.add(segment.fingerprint);
          candidates.push(segment);
        } catch (e) {
          console.error('[VocabMeld] Segment pre-processing error:', e);
        }
      }

      if (candidates.length === 0) return;

      const combinedText = candidates.map(s => s.filteredText).join('\n\n---\n\n');
      const baseMax = INTENSITY_CONFIG[config?.intensity]?.maxPerParagraph || 8;
      const maxReplacementsOverride = Math.min(baseMax * candidates.length, 80);
      const result = await translateText(combinedText, {
        minTextLenForApi: 50,
        maxReplacementsOverride
      });

      if (result.immediate?.length) {
        for (const segment of candidates) {
          const picked = pickSegmentReplacements(result.immediate, segment, whitelistWords);
          if (picked.length === 0) continue;
          applyReplacements(segment.element, picked);
        }
      }

      if (result.async) {
        result.async.then((asyncReplacements) => {
          if (!asyncReplacements?.length) return;
          for (const segment of candidates) {
            if (!segment?.element?.isConnected) continue;
            const alreadyReplaced = new Set();
            segment.element.querySelectorAll('.vocabmeld-translated').forEach(el => {
              const original = el.getAttribute('data-original');
              if (original) alreadyReplaced.add(original.toLowerCase());
            });
            const picked = pickSegmentReplacements(asyncReplacements, segment, whitelistWords, alreadyReplaced);
            if (picked.length === 0) continue;
            applyReplacements(segment.element, picked);
          }
        }).catch((error) => {
          console.error('[VocabMeld] Async translation error:', error);
        });
      }
    } catch (e) {
      console.error('[VocabMeld] Batch processing error:', e);
    } finally {
      for (const segment of activeSegments) finalize(segment);
    }
  }

  // 处理待处理的可见容器
  const processPendingContainers = debounce(async () => {
    if (isProcessing || pendingContainers.size === 0) return;
    if (document.hidden || !isTabActive) return;
    if (!shouldProcessSite()) {
      pendingContainers.clear();
      return;
    }
    
    isProcessing = true;
    
    try {
      // Drop entries that are no longer eligible to process.
      for (const container of Array.from(pendingContainers)) {
        if (!container?.isConnected) {
          pendingContainers.delete(container);
          continue;
        }
        if (container.hasAttribute('data-vocabmeld-processed')) {
          pendingContainers.delete(container);
        }
      }
      if (pendingContainers.size === 0) return;

      const viewportHeight = window.innerHeight || 1;
      const viewportCenter = viewportHeight / 2;
      const scored = Array.from(pendingContainers).map((container) => {
        try {
          if (container.hasAttribute('data-vocabmeld-processed')) {
            return { container, score: Number.POSITIVE_INFINITY };
          }
          const rect = container.getBoundingClientRect();
          const inViewport = rect.bottom > 0 && rect.top < viewportHeight;
          const center = rect.top + rect.height / 2;
          const distance = Math.abs(center - viewportCenter);
          return { container, score: (inViewport ? 0 : 1_000_000) + distance };
        } catch {
          return { container, score: Number.POSITIVE_INFINITY };
        }
      });

      scored.sort((a, b) => a.score - b.score);

      const containers = scored
        .slice(0, MAX_SEGMENTS_PER_BATCH)
        .map(x => x.container);
      // 只移除本次要处理的容器，保留后续添加的
      for (const container of containers) {
        pendingContainers.delete(container);
      }
      
      // 收集需要处理的段落
      const segments = [];
      const whitelistWords = new Set((config.learnedWords || []).map(w => w.original.toLowerCase()));
      
      for (const container of containers) {
        // 移除观察标记
        container.removeAttribute('data-vocabmeld-observing');
        
        if (container.hasAttribute('data-vocabmeld-processed')) continue;
        const text = getTextContent(container);
        const isBiliComment = isLikelyBilibiliCommentContainer(container);
        const minLen = isBiliComment ? 10 : 50;
        if (!text || text.length < minLen) continue;
        if (isCodeText(text)) continue;
        
        const path = getElementPath(container);
        const fingerprint = generateFingerprint(text, path);
        if (container.getAttribute(SCANNED_ATTR) === fingerprint) continue;
        if (processedFingerprints.has(fingerprint)) continue;
        
        // 过滤白名单词汇（单次扫描，避免为每个词构造/执行正则）
        let filteredText = text;
        if (whitelistWords.size > 0) {
          filteredText = filteredText
            .replace(/\b[a-zA-Z][a-zA-Z'-]*\b/g, (m) => (whitelistWords.has(m.toLowerCase()) ? '' : m))
            .replace(/\s+/g, ' ');
        }
        
        const minFilteredLen = isBiliComment ? 10 : 30;
        if (filteredText.trim().length >= minFilteredLen) {
          segments.push({
            element: container,
            text: text.slice(0, 2000),
            filteredText,
            fingerprint,
            path,
            minTextLenForApi: isBiliComment ? 10 : 50,
            maxReplacementsCap: isBiliComment ? 2 : Infinity
          });
        }
      }

      // 分批处理：合并段落减少 API 请求频率（仅对标准段落生效，避免影响短文本/评论场景）
      const mergeable = [];
      const individual = [];
      for (const segment of segments) {
        const canMerge =
          segment.minTextLenForApi === 50 &&
          segment.maxReplacementsCap === Infinity;
        (canMerge ? mergeable : individual).push(segment);
      }

      for (let i = 0; i < mergeable.length; i += MAX_SEGMENTS_PER_REQUEST) {
        const batch = mergeable.slice(i, i + MAX_SEGMENTS_PER_REQUEST);
        await processBatchSegments(batch, whitelistWords);
        if (i + MAX_SEGMENTS_PER_REQUEST < mergeable.length) {
          await new Promise(resolve => setTimeout(resolve, REQUEST_INTERVAL_MS));
        }
      }

      for (let i = 0; i < individual.length; i += MAX_CONCURRENT) {
        const batch = individual.slice(i, i + MAX_CONCURRENT);
        await Promise.all(batch.map(segment => processSegmentAsync(segment, whitelistWords)));
        if (i + MAX_CONCURRENT < individual.length) {
          await new Promise(resolve => setTimeout(resolve, PROCESS_DELAY_MS));
        }
      }
    } finally {
      isProcessing = false;
      
      // 如果还有待处理的容器，继续处理
      if (pendingContainers.size > 0) {
        processPendingContainers();
      }
    }
  }, 100);

  // 异步处理单个段落
  async function processSegmentAsync(segment, whitelistWords) {
    if (segment.element.hasAttribute(PROCESSING_ATTR)) return;
    segment.element.setAttribute(PROCESSING_ATTR, 'true');

    try {
      // 段落翻译：命中则整段翻译并后置原文，避免再做词汇替换
      const paragraphApplied = await maybeIntegrateParagraphTranslation(segment.element, segment.text, segment.fingerprint);
      if (paragraphApplied) {
        processedFingerprints.add(segment.fingerprint);
        return;
      }

      // 句子翻译：命中则对段内部分句子翻译并后置对应原文
      const sentenceApplied = await maybeIntegrateSentenceTranslations(segment.element, segment.fingerprint);
      if (sentenceApplied) {
        processedFingerprints.add(segment.fingerprint);
      }

      const result = await translateText(segment.filteredText, {
        minTextLenForApi: segment.minTextLenForApi,
        maxReplacementsCap: segment.maxReplacementsCap
      });

      // 先应用缓存结果
      if (result.immediate?.length) {
        const filtered = result.immediate.filter(r => !whitelistWords.has(r.original.toLowerCase()));
        const count = applyReplacements(segment.element, filtered);
        if (count > 0) {
          processedFingerprints.add(segment.fingerprint);
        }
      }

      // 异步结果
      if (result.async) {
        result.async.then(asyncReplacements => {
          if (asyncReplacements?.length) {
            const alreadyReplaced = new Set();
            segment.element.querySelectorAll('.vocabmeld-translated').forEach(el => {
              const original = el.getAttribute('data-original');
              if (original) alreadyReplaced.add(original.toLowerCase());
            });

            const filtered = asyncReplacements.filter(r =>
              !whitelistWords.has(r.original.toLowerCase()) &&
              !alreadyReplaced.has(r.original.toLowerCase())
            );

            if (filtered.length > 0) {
              const count = applyReplacements(segment.element, filtered);
              if (count > 0) {
                processedFingerprints.add(segment.fingerprint);
              }
            }
          }
        }).catch(error => {
          console.error('[VocabMeld] Async translation error:', error);
        });
      }
    } catch (e) {
      console.error('[VocabMeld] Segment error:', e);
    } finally {
      segment.element.removeAttribute(PROCESSING_ATTR);
      // Prevent repeatedly re-processing the same content; if the text changes, fingerprint changes.
      processedFingerprints.add(segment.fingerprint);
      segment.element.setAttribute(SCANNED_ATTR, segment.fingerprint);
    }
  }

  // 检查元素是否在视口内
  function isInViewport(element, margin = VIEWPORT_PREFETCH_MARGIN_PX) {
    const rect = element.getBoundingClientRect();
    const viewportHeight = window.innerHeight;
    return rect.bottom >= -margin && rect.top <= viewportHeight + margin;
  }

  // 观察页面中的文本容器
  function observeTextContainers() {
    if (!intersectionObserver) return;
    if (document.hidden || !isTabActive) return;
    if (!shouldProcessSite()) return;
    
    const containers = findTextContainers(document.body);
    let hasVisibleUnprocessed = false;
    
    for (const container of containers) {
      // 跳过已处理的容器
      if (container.hasAttribute('data-vocabmeld-processed')) {
        continue;
      }
      // 跳过正在处理的容器
      if (container.hasAttribute(PROCESSING_ATTR)) {
        continue;
      }
      
      // 检查是否在视口内且未被处理
      if (isInViewport(container)) {
        // 已经在视口内的容器，直接添加到待处理队列
        if (!container.hasAttribute('data-vocabmeld-observing')) {
          pendingContainers.add(container);
          container.setAttribute('data-vocabmeld-observing', 'true');
          hasVisibleUnprocessed = true;
        }
      }
      
      // 观察所有未处理的容器（用于后续滚动）
      if (!observedContainers.has(container)) {
        intersectionObserver.observe(container);
        observedContainers.add(container);
      }
    }
    
    // 如果有可见但未处理的容器，立即触发处理
    if (hasVisibleUnprocessed && config?.enabled && !isProcessing) {
      processPendingContainers();
    }
  }

  async function processPage(viewportOnly = true) {
    if (!config?.enabled) return { processed: 0, disabled: true };

    // 检查站点规则
    if (!shouldProcessSite()) return { processed: 0, excluded: true };

    // 确保缓存已加载
    if (wordCache.size === 0) {
      await loadWordCache();
    }

    // 处理记忆列表中的单词
    const memorizeWords = (config.memorizeList || []).map(w => w.word).filter(w => w && w.trim());
    if (memorizeWords.length > 0) {
      processSpecificWords(memorizeWords).catch(console.error);
    }

    // 使用 IntersectionObserver 懒加载
    observeTextContainers();

    return { processed: 0, lazy: true };
  }

  // ============ UI 组件 ============
  function createTooltip() {
    if (tooltip) return;
    
    tooltip = document.createElement('div');
    tooltip.className = 'vocabmeld-tooltip';
    tooltip.setAttribute('data-theme', config?.theme || 'dark');
    tooltip.style.display = 'none';
    document.body.appendChild(tooltip);
  }

  function getWordQueryDefinitionDisplayMode() {
    const mode = String(config?.wordQueryDefinitionDisplay || 'both').trim().toLowerCase();
    if (mode === 'en' || mode === 'zh' || mode === 'both') return mode;
    return 'both';
  }

  function getWordQueryTitleText() {
    const mode = getWordQueryDefinitionDisplayMode();
    const suffix = mode === 'en' ? '英文释义' : mode === 'zh' ? '中文释义' : '中英释义';
    return `AI 查询（${suffix}）`;
  }

  function buildTooltipQueryHtmlDisabled() {
    return `
      <div class="vocabmeld-tooltip-query-title">AI 查询</div>
      <div class="vocabmeld-tooltip-query-status">未启用（设置 → API 配置 → 查询配置）</div>
    `;
  }

  function buildTooltipQueryHtmlNotConfigured() {
    return `
      <div class="vocabmeld-tooltip-query-title">AI 查询</div>
      <div class="vocabmeld-tooltip-query-status">未配置查询 API</div>
    `;
  }

  function buildTooltipQueryHtmlLoading() {
    return `
      <div class="vocabmeld-tooltip-query-title">${getWordQueryTitleText()}</div>
      <div class="vocabmeld-tooltip-query-status">加载中…</div>
    `;
  }

  function buildTooltipQueryHtmlStreaming(previewText) {
    const shown = String(previewText || '').slice(0, 4000);
    return `
      <div class="vocabmeld-tooltip-query-title">${getWordQueryTitleText()}</div>
      <div class="vocabmeld-tooltip-query-status">生成中…</div>
      <pre class="vocabmeld-tooltip-query-stream">${escapeHtml(shown)}</pre>
    `;
  }

  function buildTooltipQueryHtmlError(message) {
    return `
      <div class="vocabmeld-tooltip-query-title">${getWordQueryTitleText()}</div>
      <div class="vocabmeld-tooltip-query-status vocabmeld-tooltip-query-error">查询失败：${escapeHtml(message || '')}</div>
    `;
  }

  function buildTooltipQueryHtmlData(data, { statusText = '', isPartial = false } = {}) {
    const safeWord = escapeHtml(data?.word || '');
    const parts = Array.isArray(data?.parts_of_speech) ? data.parts_of_speech : [];
    const meaningsEn = Array.isArray(data?.meanings_en) ? data.meanings_en : (Array.isArray(data?.meanings) ? data.meanings : []);
    const meaningsZh = Array.isArray(data?.meanings_zh) ? data.meanings_zh : [];
    const inflections = Array.isArray(data?.inflections) ? data.inflections : [];
    const collocations = Array.isArray(data?.collocations) ? data.collocations : [];
    const displayMode = getWordQueryDefinitionDisplayMode();

    const partsLine = parts.length
      ? `<div class="vocabmeld-tooltip-query-meta"><span class="vocabmeld-tooltip-query-label">POS</span> ${escapeHtml(parts.join(', '))}</div>`
      : '';

    const byPosEn = new Map(
      meaningsEn
        .filter(m => m && typeof m === 'object')
        .map(m => [String(m.pos || '').trim(), Array.isArray(m.definitions) ? m.definitions : []])
        .filter(([pos]) => Boolean(pos))
    );
    const byPosZh = new Map(
      meaningsZh
        .filter(m => m && typeof m === 'object')
        .map(m => [String(m.pos || '').trim(), Array.isArray(m.definitions) ? m.definitions : []])
        .filter(([pos]) => Boolean(pos))
    );

    const posOrder = [];
    for (const pos of byPosEn.keys()) posOrder.push(pos);
    for (const pos of byPosZh.keys()) if (!byPosEn.has(pos)) posOrder.push(pos);

    const renderDefs = (defs, { label = '', variant = 'en' } = {}) => {
      const shown = (Array.isArray(defs) ? defs : []).filter(Boolean).slice(0, 8);
      if (shown.length === 0) return '';
      const labelHtml = label ? `<div class="vocabmeld-tooltip-query-defs-label">${escapeHtml(label)}</div>` : '';
      const textClass = variant === 'zh' ? 'vocabmeld-tooltip-query-def-text vocabmeld-tooltip-query-def-text-zh' : 'vocabmeld-tooltip-query-def-text';
      return `
        <div class="vocabmeld-tooltip-query-defs-block">
          ${labelHtml}
          <div class="vocabmeld-tooltip-query-defs">
            ${shown.map((d, idx) => `
              <div class="vocabmeld-tooltip-query-def-item">
                <span class="vocabmeld-tooltip-query-def-idx">${idx + 1}.</span>
                <span class="${textClass}">${escapeHtml(d)}</span>
              </div>
            `).join('')}
          </div>
        </div>
      `;
    };

    const meaningsHtml = posOrder.length
      ? posOrder.map((rawPos) => {
          const pos = escapeHtml(rawPos);
          const defsEn = byPosEn.get(rawPos) || [];
          const defsZh = byPosZh.get(rawPos) || [];

          const enBlock = displayMode !== 'zh'
            ? renderDefs(defsEn, { label: displayMode === 'both' ? '英文' : '', variant: 'en' })
            : '';
          const zhBlock = displayMode !== 'en'
            ? renderDefs(defsZh, { label: displayMode === 'both' ? '中文' : '', variant: 'zh' })
            : '';

          if (!enBlock && !zhBlock) return '';
          return `
            <div class="vocabmeld-tooltip-query-sense">
              ${pos ? `<div class="vocabmeld-tooltip-query-pos">${pos}</div>` : ''}
              ${enBlock}
              ${zhBlock}
            </div>
          `;
        }).filter(Boolean).join('')
      : `<div class="vocabmeld-tooltip-query-status">${isPartial ? '等待内容…' : '暂无结果'}</div>`;

    const inflectionsHtml = inflections.length
      ? `<div class="vocabmeld-tooltip-query-meta"><span class="vocabmeld-tooltip-query-label">Inflections</span> ${escapeHtml(inflections.join(' · '))}</div>`
      : '';

    const shownCollocations = Array.isArray(collocations) ? collocations.filter(Boolean).slice(0, 5) : [];
    const collocationsHtml = shownCollocations.length
      ? `<div class="vocabmeld-tooltip-query-chips">${shownCollocations.map(c => `<span class="vocabmeld-tooltip-query-chip">${escapeHtml(c)}</span>`).join('')}</div>`
      : '';

    return `
      <div class="vocabmeld-tooltip-query-title">${getWordQueryTitleText()}</div>
      ${statusText ? `<div class="vocabmeld-tooltip-query-status">${escapeHtml(statusText)}</div>` : ''}
      ${safeWord ? `<div class="vocabmeld-tooltip-query-word">${safeWord}</div>` : ''}
      ${partsLine}
      ${meaningsHtml}
      ${inflectionsHtml}
      ${collocationsHtml}
    `;
  }

  function getLangFamily(code) {
    const c = String(code || '').toLowerCase();
    if (c.startsWith('zh')) return 'zh';
    return c;
  }

  function isWordInConfiguredTargetLanguage(word) {
    if (!word) return false;
    const family = getLangFamily(config?.targetLanguage);
    if (!family) return false;
    return detectLanguage(word) === family;
  }

  function pickExplainWord(original, translation) {
    if (isWordInConfiguredTargetLanguage(original)) return original;
    if (isWordInConfiguredTargetLanguage(translation)) return translation;
    return translation || original || '';
  }

  function getExplainToggleIconSvg(nextMode, size = 16) {
    const s = Number(size) || 16;
    // Book icon for dict, sparkle icon for ai.
    if (nextMode === 'dict') {
      return `
        <svg viewBox="0 0 24 24" width="${s}" height="${s}" aria-hidden="true">
          <path fill="currentColor" d="M18 2H7a3 3 0 0 0-3 3v15a2 2 0 0 0 2 2h12v-2H6V5a1 1 0 0 1 1-1h11v8h2V4a2 2 0 0 0-2-2z"/>
          <path fill="currentColor" d="M20 14H8a2 2 0 0 0-2 2v6h14a2 2 0 0 0 2-2v-4a2 2 0 0 0-2-2zm0 6H8v-4h12v4z"/>
        </svg>
      `;
    }
    return `
      <svg viewBox="0 0 24 24" width="${s}" height="${s}" aria-hidden="true">
        <path fill="currentColor" d="M12 2l1.9 6.6L20.5 10l-6.6 1.9L12 18.5l-1.9-6.6L3.5 10l6.6-1.4L12 2z"/>
        <path fill="currentColor" d="M5 20l.9-3 3-.9-3-.9L5 12l-.9 3-3 .9 3 .9L5 20z"/>
      </svg>
    `;
  }

  function updateExplainToggleButton(button, currentMode) {
    if (!button) return;
    const nextMode = currentMode === 'ai' ? 'dict' : 'ai';
    button.dataset.nextMode = nextMode;
    button.title = nextMode === 'dict' ? '切换到词典解释' : '切换到 AI 解释';
    button.innerHTML = getExplainToggleIconSvg(nextMode, 16);
  }

  function startTooltipWordQueryStream(queryWord, queryKey) {
    if (!queryWord || !queryKey) return;
    let hasStructuredUpdate = false;

    const stream = prefetchWordQueryStreaming(queryWord, {
      onPartialData: (partial) => {
        hasStructuredUpdate = true;
        if (!tooltip || tooltip.style.display !== 'block') return;
        if (tooltip.dataset.wordQueryKey !== queryKey) return;
        const liveContainer = tooltip.querySelector('.vocabmeld-tooltip-query');
        if (!liveContainer) return;
        liveContainer.innerHTML = buildTooltipQueryHtmlData(partial, { statusText: '生成中…', isPartial: true });
      },
      onRawText: (text) => {
        if (hasStructuredUpdate) return;
        if (!tooltip || tooltip.style.display !== 'block') return;
        if (tooltip.dataset.wordQueryKey !== queryKey) return;
        const liveContainer = tooltip.querySelector('.vocabmeld-tooltip-query');
        if (!liveContainer) return;
        liveContainer.innerHTML = buildTooltipQueryHtmlStreaming(text);
      }
    });

    activeWordQueryStream = { key: queryKey, cancel: stream.cancel };

    stream.promise.then((data) => {
      if (!tooltip || tooltip.style.display !== 'block') return;
      if (tooltip.dataset.wordQueryKey !== queryKey) return;
      const finalContainer = tooltip.querySelector('.vocabmeld-tooltip-query');
      if (finalContainer) finalContainer.innerHTML = buildTooltipQueryHtmlData(data);
    }).catch((err) => {
      if (!tooltip || tooltip.style.display !== 'block') return;
      if (tooltip.dataset.wordQueryKey !== queryKey) return;
      const errorContainer = tooltip.querySelector('.vocabmeld-tooltip-query');
      if (errorContainer) errorContainer.innerHTML = buildTooltipQueryHtmlError(err?.message || String(err));
    });
  }

  function ensureTooltipDictionaryLoaded() {
    if (!tooltip || tooltip.style.display !== 'block') return;
    const dictContainer = tooltip.querySelector('.vocabmeld-tooltip-dict');
    if (!dictContainer) return;
    const dictWord = tooltip.dataset.dictWord || '';
    if (!dictWord) {
      dictContainer.innerHTML = buildTooltipDictHtmlEmpty('');
      return;
    }
    if (detectLanguage(dictWord) !== 'en') {
      dictContainer.innerHTML = buildTooltipDictHtmlUnsupported(dictWord);
      return;
    }

    const dictionaryType = config?.dictionaryType || 'zh-en';
    const cacheKey = `${dictWord.toLowerCase()}_${dictionaryType}`;
    tooltip.dataset.dictCacheKey = cacheKey;

    if (dictCache.has(cacheKey)) {
      const cached = dictCache.get(cacheKey);
      dictContainer.innerHTML = cached ? buildTooltipDictHtmlData(cached) : buildTooltipDictHtmlEmpty(dictWord);
      return;
    }

    dictContainer.innerHTML = buildTooltipDictHtmlLoading(dictWord);
    fetchDictionaryData(dictWord).then((dictData) => {
      if (!tooltip || tooltip.style.display !== 'block') return;
      if (tooltip.dataset.dictCacheKey !== cacheKey) return;
      dictContainer.innerHTML = dictData ? buildTooltipDictHtmlData(dictData) : buildTooltipDictHtmlEmpty(dictWord);
    }).catch((err) => {
      if (!tooltip || tooltip.style.display !== 'block') return;
      if (tooltip.dataset.dictCacheKey !== cacheKey) return;
      dictContainer.innerHTML = buildTooltipDictHtmlError(dictWord, err?.message || String(err));
    });
  }

  function ensureTooltipAiLoaded() {
    if (!tooltip || tooltip.style.display !== 'block') return;
    const queryContainer = tooltip.querySelector('.vocabmeld-tooltip-query');
    if (!queryContainer) return;
    const queryWord = tooltip.dataset.wordQueryWord || '';
    const queryKey = tooltip.dataset.wordQueryKey || '';

    if (!config?.enableWordQuery) {
      queryContainer.innerHTML = buildTooltipQueryHtmlDisabled();
      return;
    }
    if (!config?.queryApiEndpoint || !config?.queryModelName) {
      queryContainer.innerHTML = buildTooltipQueryHtmlNotConfigured();
      return;
    }
    if (queryKey && wordQueryCache.get(queryKey)?.data) {
      queryContainer.innerHTML = buildTooltipQueryHtmlData(wordQueryCache.get(queryKey).data);
      return;
    }
    if (!queryKey) {
      queryContainer.innerHTML = buildTooltipQueryHtmlError('无效单词');
      return;
    }

    queryContainer.innerHTML = buildTooltipQueryHtmlLoading();
    startTooltipWordQueryStream(queryWord, queryKey);
  }

  function setTooltipExplainMode(mode) {
    if (!tooltip) return;
    const aiContainer = tooltip.querySelector('.vocabmeld-tooltip-query');
    const dictContainer = tooltip.querySelector('.vocabmeld-tooltip-dict');
    if (!aiContainer || !dictContainer) return;

    const next = mode === 'dict' ? 'dict' : 'ai';
    tooltipExplainMode = next;
    tooltip.dataset.explainMode = next;
    aiContainer.style.display = next === 'ai' ? 'block' : 'none';
    dictContainer.style.display = next === 'dict' ? 'block' : 'none';
    updateExplainToggleButton(tooltip.querySelector('.vocabmeld-btn-explain-toggle'), next);

    if (next === 'dict') ensureTooltipDictionaryLoaded();
    else ensureTooltipAiLoaded();
  }

  function showTooltip(element, mouseX = null, mouseY = null) {
    if (!tooltip || !element.classList?.contains('vocabmeld-translated')) return;

    const original = element.getAttribute('data-original');
    const translation = element.getAttribute('data-translation');
    const phonetic = element.getAttribute('data-phonetic');
    const difficulty = element.getAttribute('data-difficulty');
    
    // 检查是否已在记忆列表中
    const originalLower = String(original || '').toLowerCase();
    const isInMemorizeList = (config.memorizeList || []).some(w => 
      String(w.word || '').toLowerCase() === originalLower
    );

    const explainWord = pickExplainWord(original, translation);
    const queryWord = normalizeWordQueryText(explainWord);
    const queryKey = makeWordQueryCacheKey(queryWord);
    tooltip.dataset.wordQueryKey = queryKey;
    tooltip.dataset.wordQueryWord = queryWord;

    if (activeWordQueryStream?.key && activeWordQueryStream.key !== queryKey) {
      try { activeWordQueryStream.cancel?.(); } catch {}
      activeWordQueryStream = null;
    }

    let queryInnerHtml = '';
    if (!config?.enableWordQuery) {
      queryInnerHtml = buildTooltipQueryHtmlDisabled();
    } else if (!config?.queryApiEndpoint || !config?.queryModelName) {
      queryInnerHtml = buildTooltipQueryHtmlNotConfigured();
    } else if (queryKey && wordQueryCache.get(queryKey)?.data) {
      queryInnerHtml = buildTooltipQueryHtmlData(wordQueryCache.get(queryKey).data);
    } else if (queryKey) {
      queryInnerHtml = buildTooltipQueryHtmlLoading();
    } else {
      queryInnerHtml = buildTooltipQueryHtmlError('无效单词');
    }

    const dictWord = normalizeWordQueryText(explainWord);
    const dictCacheKey = dictWord ? `${dictWord.toLowerCase()}_${config?.dictionaryType || 'zh-en'}` : '';
    tooltip.dataset.dictWord = dictWord;
    tooltip.dataset.dictCacheKey = dictCacheKey;

    let dictInnerHtml = '';
    if (!dictWord) {
      dictInnerHtml = buildTooltipDictHtmlEmpty('');
    } else if (detectLanguage(dictWord) !== 'en') {
      dictInnerHtml = buildTooltipDictHtmlUnsupported(dictWord);
    } else if (dictCacheKey && dictCache.has(dictCacheKey)) {
      const cached = dictCache.get(dictCacheKey);
      dictInnerHtml = cached ? buildTooltipDictHtmlData(cached) : buildTooltipDictHtmlEmpty(dictWord);
    } else {
      dictInnerHtml = buildTooltipDictHtmlLoading(dictWord);
    }

    let initialExplainMode = tooltipExplainMode;
    if (initialExplainMode !== 'dict') initialExplainMode = 'ai';
    if (initialExplainMode === 'ai' && (!config?.enableWordQuery || !config?.queryApiEndpoint || !config?.queryModelName)) {
      initialExplainMode = 'dict';
    }

    tooltip.innerHTML = `
      <div class="vocabmeld-tooltip-header">
        <span class="vocabmeld-tooltip-word">${escapeHtml(translation)}</span>
        <span class="vocabmeld-tooltip-badge">${escapeHtml(difficulty)}</span>
      </div>
      ${phonetic && config.showPhonetic ? `<div class="vocabmeld-tooltip-phonetic">${escapeHtml(phonetic)}</div>` : ''}
      <div class="vocabmeld-tooltip-original">原文: ${escapeHtml(original)}</div>
      <div class="vocabmeld-tooltip-query" style="display: ${initialExplainMode === 'ai' ? 'block' : 'none'};">${queryInnerHtml}</div>
      <div class="vocabmeld-tooltip-dict" style="display: ${initialExplainMode === 'dict' ? 'block' : 'none'};">${dictInnerHtml}</div>
      <div class="vocabmeld-tooltip-actions">
        <button class="vocabmeld-tooltip-btn vocabmeld-btn-explain-toggle" title="">
        </button>
        <button class="vocabmeld-tooltip-btn vocabmeld-btn-speak" data-original="${escapeHtml(original)}" data-translation="${escapeHtml(translation)}" title="发音">
          <svg viewBox="0 0 24 24" width="16" height="16">
            <path fill="currentColor" d="M14,3.23V5.29C16.89,6.15 19,8.83 19,12C19,15.17 16.89,17.84 14,18.7V20.77C18,19.86 21,16.28 21,12C21,7.72 18,4.14 14,3.23M16.5,12C16.5,10.23 15.5,8.71 14,7.97V16C15.5,15.29 16.5,13.76 16.5,12M3,9V15H7L12,20V4L7,9H3Z"/>
          </svg>
        </button>
        <button class="vocabmeld-tooltip-btn vocabmeld-btn-memorize ${isInMemorizeList ? 'active' : ''}" data-original="${escapeHtml(original)}" title="${isInMemorizeList ? '已在记忆列表' : '添加到记忆列表'}">
          <svg viewBox="0 0 24 24" width="16" height="16">
            ${isInMemorizeList 
              ? '<path fill="currentColor" d="M12,21.35L10.55,20.03C5.4,15.36 2,12.27 2,8.5C2,5.41 4.42,3 7.5,3C9.24,3 10.91,3.81 12,5.08C13.09,3.81 14.76,3 16.5,3C19.58,3 22,5.41 22,8.5C22,12.27 18.6,15.36 13.45,20.03L12,21.35Z"/>'
              : '<path fill="currentColor" d="M12.1,18.55L12,18.65L11.89,18.55C7.14,14.24 4,11.39 4,8.5C4,6.5 5.5,5 7.5,5C9.04,5 10.54,6 11.07,7.36H12.93C13.46,6 14.96,5 16.5,5C18.5,5 20,6.5 20,8.5C20,11.39 16.86,14.24 12.1,18.55M16.5,3C14.76,3 13.09,3.81 12,5.08C10.91,3.81 9.24,3 7.5,3C4.42,3 2,5.41 2,8.5C2,12.27 5.4,15.36 10.55,20.03L12,21.35L13.45,20.03C18.6,15.36 22,12.27 22,8.5C22,5.41 19.58,3 16.5,3Z"/>'
            }
          </svg>
        </button>
        <button class="vocabmeld-tooltip-btn vocabmeld-btn-learned" data-original="${escapeHtml(original)}" data-translation="${escapeHtml(translation)}" data-difficulty="${escapeHtml(difficulty)}" title="标记已学会">
          <svg viewBox="0 0 24 24" width="16" height="16">
            <path fill="currentColor" d="M21,7L9,19L3.5,13.5L4.91,12.09L9,16.17L19.59,5.59L21,7Z"/>
          </svg>
        </button>
        <button class="vocabmeld-tooltip-btn vocabmeld-btn-retry" data-word="${escapeHtml(queryWord)}" ${(!config?.enableWordQuery || !config?.queryApiEndpoint || !config?.queryModelName || !queryKey) ? 'disabled' : ''} title="重新查询释义/变形">
          <svg viewBox="0 0 24 24" width="16" height="16">
            <path fill="currentColor" d="M12,6V9L16,5L12,1V4A8,8 0 0,0 4,12H6A6,6 0 0,1 12,6M18,12A6,6 0 0,1 12,18V15L8,19L12,23V20A8,8 0 0,0 20,12H18Z"/>
          </svg>
        </button>
      </div>
    `;

    positionTooltipForElement(element, mouseX, mouseY);
    tooltip.style.display = 'block';
    activeTooltipTarget = element;

    updateExplainToggleButton(tooltip.querySelector('.vocabmeld-btn-explain-toggle'), initialExplainMode);
    setTooltipExplainMode(initialExplainMode);
  }

  function positionTooltipForElement(element, mouseX = null, mouseY = null) {
    if (!tooltip || !element?.getBoundingClientRect) return;
    let posLeft;
    let posTop;

    try {
      if (typeof mouseX === 'number' && typeof mouseY === 'number' && typeof document.caretRangeFromPoint === 'function') {
        const caretRange = document.caretRangeFromPoint(mouseX, mouseY);
        if (caretRange && element.contains(caretRange.startContainer)) {
          const tempRange = document.createRange();
          tempRange.setStart(caretRange.startContainer, caretRange.startOffset);
          tempRange.setEnd(caretRange.startContainer, caretRange.startOffset);
          const caretRect = tempRange.getBoundingClientRect();

          const textNode = caretRange.startContainer;
          if (textNode?.nodeType === Node.TEXT_NODE) {
            let lineStartOffset = 0;
            for (let i = caretRange.startOffset; i >= 0; i--) {
              tempRange.setStart(textNode, i);
              tempRange.setEnd(textNode, Math.min(textNode.length, i + 1));
              const charRect = tempRange.getBoundingClientRect();
              if (Math.abs(charRect.top - caretRect.top) > 5) {
                lineStartOffset = i + 1;
                break;
              }
              lineStartOffset = i;
            }
            tempRange.setStart(textNode, lineStartOffset);
            tempRange.setEnd(textNode, Math.min(textNode.length, lineStartOffset + 1));
            const lineStartRect = tempRange.getBoundingClientRect();
            posLeft = lineStartRect.left;
            posTop = caretRect.bottom;
          } else {
            posLeft = caretRect.left;
            posTop = caretRect.bottom;
          }
        }
      }
    } catch {}

    if (posLeft === undefined || posTop === undefined) {
      const rect = element.getBoundingClientRect();
      posLeft = rect.left;
      posTop = rect.bottom;
      if (typeof mouseY === 'number') posTop = Math.max(posTop, mouseY + 10);
    }

    tooltip.style.left = `${posLeft + window.scrollX}px`;
    tooltip.style.top = `${posTop + window.scrollY + 2}px`;
  }

  function refreshTooltipPosition() {
    if (!tooltip || tooltip.style.display !== 'block') return;
    if (!activeTooltipTarget || !document.contains(activeTooltipTarget)) {
      hideTooltip(true);
      return;
    }
    positionTooltipForElement(activeTooltipTarget);
  }

  function elementHasDirectNonWhitespaceText(el) {
    if (!el?.childNodes) return false;
    for (const node of Array.from(el.childNodes)) {
      if (node?.nodeType === Node.TEXT_NODE && String(node.nodeValue || '').trim()) {
        return true;
      }
    }
    return false;
  }

  function isBlankClickTarget(target) {
    const el = target?.nodeType === Node.TEXT_NODE ? target.parentElement : target;
    if (!el || el === document) return true;
    if (el === document.body || el === document.documentElement) return true;
    if (el.isContentEditable) return false;
    if (el.closest?.('a,button,input,textarea,select,option,label,summary,[role="button"],[role="link"]')) return false;
    // If the clicked element itself contains meaningful text, treat as non-blank.
    if (elementHasDirectNonWhitespaceText(el)) return false;
    return true;
  }

  function hideTooltip(immediate = false) {
    if (immediate) {
      clearTimeout(tooltipHideTimeout);
      if (tooltip) tooltip.style.display = 'none';
      activeTooltipTarget = null;
      if (tooltip) tooltip.dataset.wordQueryKey = '';
      if (tooltip) tooltip.dataset.wordQueryWord = '';
      activeWordQueryStream = null;
    } else {
      // 延迟隐藏，给用户时间移动到 tooltip 上
      tooltipHideTimeout = setTimeout(() => {
        if (tooltip) tooltip.style.display = 'none';
        activeTooltipTarget = null;
        if (tooltip) tooltip.dataset.wordQueryKey = '';
        if (tooltip) tooltip.dataset.wordQueryWord = '';
        activeWordQueryStream = null;
      }, 200);
    }
  }
  
  function cancelHideTooltip() {
    clearTimeout(tooltipHideTimeout);
  }

  function showToast(message) {
    const toast = document.createElement('div');
    toast.className = 'vocabmeld-toast';
    toast.textContent = message;
    document.body.appendChild(toast);
    setTimeout(() => toast.classList.add('vocabmeld-toast-show'), 10);
    setTimeout(() => {
      toast.classList.remove('vocabmeld-toast-show');
      setTimeout(() => toast.remove(), 300);
    }, 2000);
  }

  function createSelectionPopup() {
    if (selectionPopup) return;
    
    selectionPopup = document.createElement('div');
    selectionPopup.className = 'vocabmeld-selection-popup';
    selectionPopup.setAttribute('data-theme', config?.theme || 'dark');
    selectionPopup.style.display = 'none';
    selectionPopup.innerHTML = '<button class="vocabmeld-add-memorize">添加到需记忆</button>';
    document.body.appendChild(selectionPopup);

    selectionPopup.querySelector('button').addEventListener('click', async () => {
      const selection = window.getSelection();
      const text = selection.toString().trim();
      if (text && text.length < 50) {
        await addToMemorizeList(text);
        showToast(`"${text}" 已添加到需记忆列表`);
      }
      selectionPopup.style.display = 'none';
    });
  }

  // ============ 事件处理 ============
  function setupEventListeners() {
    // 悬停预取：鼠标移动到翻译词汇上，延迟触发 AI 查询（不弹出）
    document.addEventListener('mouseover', (e) => {
      const target = e.target.closest?.('.vocabmeld-translated');
      if (!target) return;
      if (e.relatedTarget && target.contains(e.relatedTarget)) return;
      if (!config?.enableWordQuery) return;

      const original = target.getAttribute('data-original') || '';
      const translation = target.getAttribute('data-translation') || '';
      const word = pickExplainWord(original, translation);
      const key = makeWordQueryCacheKey(word);
      if (!key) return;

      clearTimeout(wordQueryHoverTimer);
      lastWordQueryHoverKey = key;
      wordQueryHoverTimer = setTimeout(() => {
        // Cancel previous hover stream (if any)
        if (wordQueryHoverStream?.cancel && wordQueryHoverStream.key !== key) {
          try { wordQueryHoverStream.cancel(); } catch {}
        }
        const s = prefetchWordQueryStreaming(word, {});
        wordQueryHoverStream = { key, cancel: s.cancel };
        s.promise.catch(() => {});
      }, WORD_QUERY_HOVER_DELAY_MS);
    }, { passive: true });

    document.addEventListener('mouseout', (e) => {
      const target = e.target.closest?.('.vocabmeld-translated');
      if (!target) return;
      if (e.relatedTarget && target.contains(e.relatedTarget)) return;
      clearTimeout(wordQueryHoverTimer);
      lastWordQueryHoverKey = '';

      // If tooltip is not showing this key, cancel hover stream to avoid "stuck" in-flight
      if (wordQueryHoverStream?.key) {
        const tooltipKey = tooltip?.dataset?.wordQueryKey || '';
        if (!tooltipKey || tooltipKey !== wordQueryHoverStream.key) {
          try { wordQueryHoverStream.cancel?.(); } catch {}
          wordQueryHoverStream = null;
        }
      }
    }, { passive: true });

    // tooltip 按钮点击事件
    document.addEventListener('click', (e) => {
      const clickTarget = e.target;

      const retryBtn = e.target.closest?.('.vocabmeld-btn-retry');
      if (retryBtn) {
        e.preventDefault();
        e.stopPropagation();
        const fallbackOriginal = activeTooltipTarget?.getAttribute?.('data-original') || '';
        const fallbackTranslation = activeTooltipTarget?.getAttribute?.('data-translation') || '';
        const word = retryBtn.getAttribute('data-word') || tooltip?.dataset?.wordQueryWord || pickExplainWord(fallbackOriginal, fallbackTranslation);
        forceRetryWordQuery(word);
        return;
      }

      const explainToggleBtn = e.target.closest?.('.vocabmeld-btn-explain-toggle');
      if (explainToggleBtn) {
        e.preventDefault();
        e.stopPropagation();
        const nextMode = explainToggleBtn.dataset.nextMode || (tooltipExplainMode === 'ai' ? 'dict' : 'ai');
        setTooltipExplainMode(nextMode);
        return;
      }

      // 发音按钮
      const speakBtn = e.target.closest('.vocabmeld-btn-speak');
      if (speakBtn) {
        e.preventDefault();
        e.stopPropagation();
        const original = speakBtn.getAttribute('data-original');
        const translation = speakBtn.getAttribute('data-translation');
        
        // 检测 original 是否是目标语言
        const originalLang = detectLanguage(original);
        const isOriginalTargetLang = (originalLang === 'en' && config.targetLanguage === 'en') ||
                                     (originalLang === 'zh' && (config.targetLanguage === 'zh-CN' || config.targetLanguage === 'zh-TW')) ||
                                     (originalLang === 'ja' && config.targetLanguage === 'ja') ||
                                     (originalLang === 'ko' && config.targetLanguage === 'ko');
        
        const word = isOriginalTargetLang ? original : translation;
        const lang = config.targetLanguage === 'en' ? 'en-US' : 
                     config.targetLanguage === 'zh-CN' ? 'zh-CN' :
                     config.targetLanguage === 'zh-TW' ? 'zh-TW' :
                     config.targetLanguage === 'ja' ? 'ja-JP' :
                     config.targetLanguage === 'ko' ? 'ko-KR' : 'en-US';
        
        chrome.runtime.sendMessage({ action: 'speak', text: word, lang });
        return;
      }
      
      // 收藏/记忆按钮
      const memorizeBtn = e.target.closest('.vocabmeld-btn-memorize');
      if (memorizeBtn) {
        e.preventDefault();
        e.stopPropagation();
        const original = memorizeBtn.getAttribute('data-original');
        const isActive = memorizeBtn.classList.contains('active');
        
        if (!isActive) {
          addToMemorizeList(original);
          memorizeBtn.classList.add('active');
          memorizeBtn.title = '已在记忆列表';
          // 更新图标为实心
          memorizeBtn.innerHTML = `
            <svg viewBox="0 0 24 24" width="16" height="16">
              <path fill="currentColor" d="M12,21.35L10.55,20.03C5.4,15.36 2,12.27 2,8.5C2,5.41 4.42,3 7.5,3C9.24,3 10.91,3.81 12,5.08C13.09,3.81 14.76,3 16.5,3C19.58,3 22,5.41 22,8.5C22,12.27 18.6,15.36 13.45,20.03L12,21.35Z"/>
            </svg>
          `;
        } else {
          removeFromMemorizeList(original);
          memorizeBtn.classList.remove('active');
          memorizeBtn.title = '添加到记忆列表';
          // 更新图标为镂空
          memorizeBtn.innerHTML = `
            <svg viewBox="0 0 24 24" width="16" height="16">
              <path fill="currentColor" d="M12.1,18.55L12,18.65L11.89,18.55C7.14,14.24 4,11.39 4,8.5C4,6.5 5.5,5 7.5,5C9.04,5 10.54,6 11.07,7.36H12.93C13.46,6 14.96,5 16.5,5C18.5,5 20,6.5 20,8.5C20,11.39 16.86,14.24 12.1,18.55M16.5,3C14.76,3 13.09,3.81 12,5.08C10.91,3.81 9.24,3 7.5,3C4.42,3 2,5.41 2,8.5C2,12.27 5.4,15.36 10.55,20.03L12,21.35L13.45,20.03C18.6,15.36 22,12.27 22,8.5C22,5.41 19.58,3 16.5,3Z"/>
            </svg>
          `;
        }
        return;
      }
      
      // 已学会按钮
      const learnedBtn = e.target.closest('.vocabmeld-btn-learned');
      if (learnedBtn) {
        e.preventDefault();
        e.stopPropagation();
        const original = learnedBtn.getAttribute('data-original');
        const translation = learnedBtn.getAttribute('data-translation');
        const difficulty = learnedBtn.getAttribute('data-difficulty') || 'B1';
        
        addToWhitelist(original, translation, difficulty);
        restoreAllSameWord(original);
        hideTooltip(true);
        showToast(`"${original}" 已标记为已学会`);
        return;
      }

      // 点击翻译词汇：显示/切换 tooltip
      const target = e.target.closest('.vocabmeld-translated');
      if (target && e.button === 0) {
        // 允许用户用 Ctrl/Meta/Shift/Alt 点击（例如打开链接）时不拦截
        if (e.ctrlKey || e.metaKey || e.shiftKey || e.altKey) return;

        // 如果词汇位于链接内，阻止跳转，优先展示 tooltip
        if (target.closest('a')) e.preventDefault();

        cancelHideTooltip();
        if (tooltip?.style.display === 'block' && activeTooltipTarget === target) {
          hideTooltip(true);
        } else {
          showTooltip(target, e.clientX, e.clientY);
        }
        return;
      }

      // 点击 tooltip 内部：不隐藏（按钮逻辑已在上面处理）
      if (e.target.closest('.vocabmeld-tooltip')) return;

      // 仅点击页面空白处才关闭 tooltip（避免滚动/点击内容时误关）
      if (isBlankClickTarget(clickTarget)) {
        hideTooltip(true);
      }
    });

    // Esc 关闭 tooltip
    document.addEventListener('keydown', (e) => {
      if (e.key === 'Escape') hideTooltip(true);
    });

    // 选择文本显示添加按钮
    document.addEventListener('mouseup', (e) => {
      if (e.target.closest('.vocabmeld-selection-popup')) return;
      
      // 如果关闭了选中添加功能，直接隐藏弹窗
      if (!config?.showAddMemorize) {
        if (selectionPopup) selectionPopup.style.display = 'none';
        return;
      }
      
      setTimeout(() => {
        const selection = window.getSelection();
        const text = selection.toString().trim();
        
        if (
          text &&
          text.length > 1 &&
          text.length < 50 &&
          !e.target.closest('.vocabmeld-translated') &&
          !e.target.closest('.vocabmeld-segment-translated')
        ) {
          const range = selection.getRangeAt(0);
          const rect = range.getBoundingClientRect();
          
          selectionPopup.style.left = rect.left + window.scrollX + 'px';
          selectionPopup.style.top = rect.bottom + window.scrollY + 5 + 'px';
          selectionPopup.style.display = 'block';
        } else {
          selectionPopup.style.display = 'none';
        }
      }, 10);
    });

    // 滚动时不关闭 tooltip，改为跟随锚点重新定位
    const handleScroll = debounce(() => {
      refreshTooltipPosition();
    }, 50);
    window.addEventListener('scroll', handleScroll, { passive: true });

    window.addEventListener('resize', debounce(() => {
      refreshTooltipPosition();
    }, 100), { passive: true });

    // 监听 DOM 变化，观察新增的文本容器
    const mutationObserver = new MutationObserver(debounce(() => {
      if (config?.autoProcess && config?.enabled && !document.hidden && isTabActive) {
        observeTextContainers();
      }
    }, 500));
    
    mutationObserver.observe(document.body, {
      childList: true,
      subtree: true
    });

    // 监听配置变化
    chrome.storage.onChanged.addListener((changes, areaName) => {
      if (areaName === 'sync') {
        loadConfig().then(() => {
          if (changes.enabled?.newValue === false) {
            restoreAll();
          }
          // 主题变化时更新 UI
          if (changes.theme) {
            updateUITheme();
          }
          // tooltip 释义显示语言变化时，立即刷新 tooltip（如果正在显示）
          if (changes.wordQueryDefinitionDisplay && tooltip && tooltip.style.display === 'block') {
            const container = tooltip.querySelector('.vocabmeld-tooltip-query');
            const queryKey = tooltip.dataset.wordQueryKey || '';
            const queryWord = tooltip.dataset.wordQueryWord || '';
            if (container) {
              let queryInnerHtml = '';
              if (!config?.enableWordQuery) {
                queryInnerHtml = buildTooltipQueryHtmlDisabled();
              } else if (!config?.queryApiEndpoint || !config?.queryModelName) {
                queryInnerHtml = buildTooltipQueryHtmlNotConfigured();
              } else if (queryKey && wordQueryCache.get(queryKey)?.data) {
                queryInnerHtml = buildTooltipQueryHtmlData(wordQueryCache.get(queryKey).data);
              } else if (queryKey && queryWord) {
                queryInnerHtml = buildTooltipQueryHtmlLoading();
              } else {
                queryInnerHtml = buildTooltipQueryHtmlError('无效单词');
              }
              container.innerHTML = queryInnerHtml;
            }
          }
          // 影响渲染/翻译结果的配置变化时，需要重新处理页面
          if (
            changes.difficultyLevel ||
            changes.intensity ||
            changes.translationStyle ||
            changes.processMode ||
            changes.apiEndpoint ||
            changes.apiKey ||
            changes.modelName ||
            changes.nativeLanguage ||
            changes.targetLanguage ||
            changes.sentenceTranslationRate ||
            changes.paragraphTranslationRate
          ) {
            restoreAll(); // 先恢复页面（会清除 processedFingerprints）
            if (config.enabled) {
              processPage(); // 重新处理
            }
          }
          // 记忆列表变化时，处理新添加的单词
          if (changes.memorizeList) {
            const oldList = changes.memorizeList.oldValue || [];
            const newList = changes.memorizeList.newValue || [];
            // 找出新添加的单词
            const oldWords = new Set(oldList.map(w => w.word.toLowerCase()));
            const newWords = newList
              .filter(w => !oldWords.has(w.word.toLowerCase()))
              .map(w => w.word);
            
              if (newWords.length > 0 && config.enabled) {
                // 延迟处理，确保DOM已更新
                setTimeout(() => {
                  processSpecificWords(newWords);
                }, 200);
              }
          }
        });
      }
    });

    // 监听来自 popup 或 background 的消息
    chrome.runtime.onMessage.addListener((message, sender, sendResponse) => {
      if (message.action === 'processPage') {
        processPage().then(sendResponse);
        return true;
      }
      if (message.action === 'restorePage') {
        restoreAll();
        sendResponse({ success: true });
      }
      if (message.action === 'processSpecificWords') {
        const words = message.words || [];
        if (words.length > 0) {
          processSpecificWords(words).then(count => {
            sendResponse({ success: true, count });
          }).catch(error => {
            console.error('[VocabMeld] Error processing specific words:', error);
            sendResponse({ success: false, error: error.message });
          });
          return true; // 保持消息通道开放以支持异步响应
        } else {
          sendResponse({ success: false, error: 'No words provided' });
        }
      }
      if (message.action === 'getStatus') {
        sendResponse({
          processed: processedFingerprints.size,
          isProcessing,
          enabled: config?.enabled
        });
      }
    });
  }

  // ============ 初始化 ============
  async function init() {
    await loadConfig();
    await loadWordCache();
    await loadWordQueryCache();

    document.addEventListener('visibilitychange', () => {
      isTabActive = !document.hidden;
      if (document.hidden) return;
      if (config?.autoProcess && config?.enabled) {
        observeTextContainers();
      }
      if (!isProcessing && pendingContainers.size > 0) {
        processPendingContainers();
      }
    });

    
    createTooltip();
    createSelectionPopup();
    
    // 初始化 IntersectionObserver
    setupIntersectionObserver();
    
    setupEventListeners();
    
    // 自动处理 - 使用 IntersectionObserver 懒加载
    if (config.autoProcess && config.enabled && config.apiEndpoint) {
      // 延迟启动，等待页面渲染完成
      setTimeout(() => {
        // 先处理记忆列表中的单词
        const memorizeWords = (config.memorizeList || []).map(w => w.word).filter(w => w && w.trim());
        if (memorizeWords.length > 0) {
          processSpecificWords(memorizeWords).catch(console.error);
        }
        // 开始观察文本容器
        observeTextContainers();
      }, 500);
    }
    
  }

  // 启动
  if (document.readyState === 'loading') {
    document.addEventListener('DOMContentLoaded', init);
  } else {
    init();
  }

})();
