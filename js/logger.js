(() => {
  if (globalThis.VocabMeldLogger) return;

  const LOG_STORAGE_KEY = 'vocabmeld_logs_v1';
  const RETENTION_DAYS_KEY = 'logRetentionDays';
  const DEFAULT_RETENTION_DAYS = 7;
  const MAX_LOG_ENTRIES = 2000;
  const MAX_SERIALIZED_ARG_CHARS = 4000;

  const ACTION_APPEND = 'vocabmeld.log.append';
  const ACTION_GET = 'vocabmeld.log.get';
  const ACTION_CLEAR = 'vocabmeld.log.clear';
  const ACTION_PRUNE = 'vocabmeld.log.prune';

  const isServiceWorker =
    typeof ServiceWorkerGlobalScope !== 'undefined' &&
    globalThis instanceof ServiceWorkerGlobalScope;

  function now() {
    return Date.now();
  }

  function clampNumber(value, min, max, fallback) {
    const n = Number(value);
    if (!Number.isFinite(n)) return fallback;
    return Math.min(max, Math.max(min, n));
  }

  function safeStringify(value) {
    if (typeof value === 'string') return value;
    if (value instanceof Error) {
      const header = `${value.name || 'Error'}: ${value.message || ''}`.trim();
      const stack = value.stack ? `\n${value.stack}` : '';
      return `${header}${stack}`.trim() || 'Error';
    }
    try {
      const seen = new WeakSet();
      return JSON.stringify(value, (key, val) => {
        if (typeof val === 'object' && val !== null) {
          if (seen.has(val)) return '[Circular]';
          seen.add(val);
        }
        if (typeof val === 'bigint') return val.toString();
        return val;
      });
    } catch {
      try {
        return String(value);
      } catch {
        return '[Unserializable]';
      }
    }
  }

  function serializeArgs(args) {
    return (args || []).map((arg) => {
      let text = safeStringify(arg);
      if (text.length > MAX_SERIALIZED_ARG_CHARS) {
        text = `${text.slice(0, MAX_SERIALIZED_ARG_CHARS)}…(truncated)`;
      }
      return text;
    });
  }

  function detectContext() {
    if (isServiceWorker) return 'background';
    if (typeof location !== 'undefined') {
      const path = location.pathname || '';
      if (location.protocol === 'chrome-extension:') {
        if (path.endsWith('/options.html') || path.endsWith('options.html')) return 'options';
        if (path.endsWith('/popup.html') || path.endsWith('popup.html')) return 'popup';
        return 'extension';
      }
      return 'content';
    }
    return 'unknown';
  }

  function storageLocalGet(key) {
    return new Promise((resolve) => {
      chrome.storage.local.get([key], (result) => resolve(result[key]));
    });
  }

  function storageLocalSet(items) {
    return new Promise((resolve, reject) => {
      chrome.storage.local.set(items, () => {
        if (chrome.runtime?.lastError) reject(chrome.runtime.lastError);
        else resolve();
      });
    });
  }

  function storageSyncGet(key) {
    return new Promise((resolve) => {
      chrome.storage.sync.get([key], (result) => resolve(result[key]));
    });
  }

  function shouldUseBackgroundWriter(context) {
    return context !== 'background';
  }

  function sendMessage(message) {
    return new Promise((resolve, reject) => {
      try {
        chrome.runtime.sendMessage(message, (response) => {
          if (chrome.runtime?.lastError) reject(chrome.runtime.lastError);
          else resolve(response);
        });
      } catch (err) {
        reject(err);
      }
    });
  }

  let initialized = false;
  let currentContext = detectContext();
  let captureInstalled = false;

  // Background-side write serialization (avoid overlapping read-modify-write).
  let writeChain = Promise.resolve();
  function enqueueWrite(fn) {
    writeChain = writeChain.then(fn, fn);
    return writeChain;
  }

  async function getRetentionDays() {
    const raw = await storageSyncGet(RETENTION_DAYS_KEY);
    return clampNumber(raw ?? DEFAULT_RETENTION_DAYS, 0, 3650, DEFAULT_RETENTION_DAYS);
  }

  function pruneLogsArray(logs, retentionDays) {
    if (!Array.isArray(logs)) return [];
    let pruned = logs;
    if (retentionDays > 0) {
      const cutoff = now() - retentionDays * 24 * 60 * 60 * 1000;
      pruned = pruned.filter((e) => (e?.ts ?? 0) >= cutoff);
    }
    if (pruned.length > MAX_LOG_ENTRIES) {
      pruned = pruned.slice(pruned.length - MAX_LOG_ENTRIES);
    }
    return pruned;
  }

  async function appendLogEntryInBackground(entry) {
    return enqueueWrite(async () => {
      const retentionDays = await getRetentionDays();
      const existing = (await storageLocalGet(LOG_STORAGE_KEY)) || [];
      const merged = pruneLogsArray(existing.concat([entry]), retentionDays);
      await storageLocalSet({ [LOG_STORAGE_KEY]: merged });
      return { total: merged.length };
    });
  }

  async function getLogsInBackground(limit = 500) {
    const retentionDays = await getRetentionDays();
    const existing = (await storageLocalGet(LOG_STORAGE_KEY)) || [];
    const pruned = pruneLogsArray(existing, retentionDays);
    if (pruned.length !== existing.length) {
      await enqueueWrite(() => storageLocalSet({ [LOG_STORAGE_KEY]: pruned }));
    }
    const normalizedLimit = clampNumber(limit, 1, 5000, 500);
    const slice = pruned.slice(Math.max(0, pruned.length - normalizedLimit));
    return { logs: slice, total: pruned.length, retentionDays };
  }

  async function clearLogsInBackground() {
    return enqueueWrite(async () => {
      await storageLocalSet({ [LOG_STORAGE_KEY]: [] });
      return { total: 0 };
    });
  }

  async function pruneLogsInBackground() {
    return enqueueWrite(async () => {
      const retentionDays = await getRetentionDays();
      const existing = (await storageLocalGet(LOG_STORAGE_KEY)) || [];
      const pruned = pruneLogsArray(existing, retentionDays);
      await storageLocalSet({ [LOG_STORAGE_KEY]: pruned });
      return { before: existing.length, after: pruned.length, retentionDays };
    });
  }

  function normalizeLevel(level) {
    const l = String(level || '').toLowerCase();
    if (l === 'warn' || l === 'warning') return 'warn';
    if (l === 'error') return 'error';
    if (l === 'debug') return 'debug';
    if (l === 'info') return 'info';
    return 'log';
  }

  function buildEntry(level, args, extra = {}) {
    const serializedArgs = serializeArgs(args);
    return {
      ts: now(),
      level: normalizeLevel(level),
      context: currentContext,
      args: serializedArgs,
      ...extra
    };
  }

  function append(level, ...args) {
    if (!initialized) init();
    const entry = buildEntry(level, args, {
      url: typeof location !== 'undefined' ? location.href : undefined
    });

    if (!chrome?.runtime?.id) return;

    if (shouldUseBackgroundWriter(currentContext)) {
      try {
        chrome.runtime.sendMessage({ action: ACTION_APPEND, entry }, () => {});
      } catch {
        // Ignore.
      }
      return;
    }

    // Background context: write directly.
    appendLogEntryInBackground(entry).catch(() => {});
  }

  function initConsoleCapture() {
    if (captureInstalled) return;
    if (typeof console === 'undefined') return;

    captureInstalled = true;

    const original = {
      log: console.log?.bind(console),
      info: console.info?.bind(console),
      warn: console.warn?.bind(console),
      error: console.error?.bind(console),
      debug: console.debug?.bind(console)
    };

    function wrap(methodName, level) {
      const originalFn = original[methodName];
      if (!originalFn) return;
      console[methodName] = (...args) => {
        try {
          append(level, ...args);
        } catch {
          // Ignore.
        }
        return originalFn(...args);
      };
    }

    wrap('log', 'log');
    wrap('info', 'info');
    wrap('warn', 'warn');
    wrap('error', 'error');
    wrap('debug', 'debug');
  }

  function init() {
    if (initialized) return;
    initialized = true;

    // Ensure the context is correct for this execution environment.
    currentContext = detectContext();
    initConsoleCapture();

    // Background-only: register message handlers so other contexts can append/read logs.
    if (currentContext === 'background') {
      pruneLogsInBackground().catch(() => {});

      chrome.runtime.onMessage.addListener((message, sender, sendResponse) => {
        if (!message || typeof message !== 'object') return;
        if (message.action === ACTION_APPEND) {
          const incoming = message.entry || {};
          const entry = {
            ...incoming,
            context: incoming.context || (sender?.url?.startsWith('chrome-extension:') ? 'extension' : 'content'),
            senderUrl: sender?.url,
            tabId: sender?.tab?.id
          };
          appendLogEntryInBackground(entry)
            .then((result) => sendResponse({ success: true, ...result }))
            .catch((err) => sendResponse({ success: false, error: err?.message || String(err) }));
          return true;
        }
        if (message.action === ACTION_GET) {
          getLogsInBackground(message.limit)
            .then((result) => sendResponse({ success: true, ...result }))
            .catch((err) => sendResponse({ success: false, error: err?.message || String(err) }));
          return true;
        }
        if (message.action === ACTION_CLEAR) {
          clearLogsInBackground()
            .then((result) => sendResponse({ success: true, ...result }))
            .catch((err) => sendResponse({ success: false, error: err?.message || String(err) }));
          return true;
        }
        if (message.action === ACTION_PRUNE) {
          pruneLogsInBackground()
            .then((result) => sendResponse({ success: true, ...result }))
            .catch((err) => sendResponse({ success: false, error: err?.message || String(err) }));
          return true;
        }
      });
    }
  }

  async function getLogs({ limit = 500 } = {}) {
    if (!initialized) init();
    if (!chrome?.runtime?.id) return { logs: [], total: 0, retentionDays: DEFAULT_RETENTION_DAYS };
    if (currentContext === 'background') return getLogsInBackground(limit);
    const response = await sendMessage({ action: ACTION_GET, limit });
    if (!response?.success) throw new Error(response?.error || 'Failed to get logs');
    return { logs: response.logs || [], total: response.total || 0, retentionDays: response.retentionDays ?? DEFAULT_RETENTION_DAYS };
  }

  async function clearLogs() {
    if (!initialized) init();
    if (!chrome?.runtime?.id) return { total: 0 };
    if (currentContext === 'background') return clearLogsInBackground();
    const response = await sendMessage({ action: ACTION_CLEAR });
    if (!response?.success) throw new Error(response?.error || 'Failed to clear logs');
    return { total: response.total || 0 };
  }

  async function pruneLogs() {
    if (!initialized) init();
    if (!chrome?.runtime?.id) return { before: 0, after: 0, retentionDays: DEFAULT_RETENTION_DAYS };
    if (currentContext === 'background') return pruneLogsInBackground();
    const response = await sendMessage({ action: ACTION_PRUNE });
    if (!response?.success) throw new Error(response?.error || 'Failed to prune logs');
    return { before: response.before || 0, after: response.after || 0, retentionDays: response.retentionDays ?? DEFAULT_RETENTION_DAYS };
  }

  globalThis.VocabMeldLogger = {
    init,
    initConsoleCapture,
    append,
    getLogs,
    clearLogs,
    pruneLogs
  };

  init();
})();
