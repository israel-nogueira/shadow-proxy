/*!
 * shadow-proxy v2.8.0
 * Reactive DOM binding via Recursive Proxy
 * https://github.com/israel-nogueira/shadow-proxy
 *
 * Directives:
 *   x-for="item in lista"                    → reactive loop (nestable)
 *   x-for="item, k in lista"                 → loop with named index alias
 *   x-for="item in lista as k"               → alternative syntax for named index
 *   x-key="item.id"                          → optional unique key for x-for
 *   x-static                                 → (filho de x-for) elemento fixo, fora do template (ex: <option value="">)
 *   x-bind="item.titulo"                     → reactive text / interpolation with {var}
 *   x-if="item.ativo"                        → reactive conditional
 *   x-on:event="expr"                        → event listener with loop scope
 *   x-model="elemento_01.nome"               → two-way binding (input/checkbox/radio/select/textarea)
 *   x-ref="nome"                             → element reference via $ref.nome
 *   x-cloak                                  → escondido até o 1º render
 *
 * Magic variables (x-on): $root, $ref.nome, $emit(name, detail), $i / $index,
 *                         $this.index / .dom / .data / .parent
 *
 * Lifecycle: $beforeRender / $afterRender / $beforeDestroy / $afterDestroy (+ DOM events)
 * Watchers : shadowProxy.on('key.prop', (newVal, oldVal) => {})
 *
 * v2.8.0 — Fixes:
 *   - Só Array/objeto literal viram proxy (Date, Map, Set, Blob... intactos)
 *   - x-for: lista vazia destrói nós (effects/listeners); scope do loop herda o store (prototype);
 *     precedência do loop sobre o store no x-on; x-model dentro do loop; filhos x-static;
 *     SVG; itens inalterados não re-renderizam nem re-bindam
 *   - Blocklist separada: identificadores livres x propriedades (item.parent / location / history / open... liberados)
 *   - Sandbox: bloqueia Window/Document em qualquer leitura, innerHTML/ownerDocument/on* em Nodes,
 *     escrita nos globais seguros, setAttribute de on* /src / href em Nodes
 * - Parser: ?. , typeof, **, 1e3, identificadores unicode
        * - set trap faz unwrap de proxies(sort / reverse / splice sem proxy dentro do raw)
 * - Atributos: "{" preservado quando não é expressão(pattern = "\d{3}", JSON); boolean attrs; value / checked sync;
 * srcdoc bloqueado
    * - x - model: path bloqueado(prototype pollution), number / range, select multiple, sem duplo bind
        * - Effects com flag dead; watchers: unsubscribe seguro, template.key = { ...} notifica
            * - Guard de loop em _scheduleApply; hooks($before...) não disparam render; ordem do $beforeRender
                * - Objetos frozen / sealed; _store / _proxies / _watchers sem prototype; x - data aninhado isolado; x - cloak
                     
 */

var shadowProxy = (function () {

    'use strict';

    const _store = Object.create(null);
    const _proxies = Object.create(null);

    const _PROXY_SYM = Symbol('shadowProxy');
    const _SCOPE_VARS = Symbol('shadowProxyScopeVars');
    const _HOOKS = new Set(['$beforeRender', '$afterRender', '$beforeDestroy', '$afterDestroy']);
    const _destroyBound = new WeakSet();

    // ─── Shadow State Store ─────────────────────────────────────────────────
    const _shadowState = new WeakMap();

    function _sGet(el, key) {
        const b = _shadowState.get(el);
        return b ? b[key] : undefined;
    }
    function _sSet(el, key, value) {
        if (!_shadowState.has(el)) _shadowState.set(el, {});
        _shadowState.get(el)[key] = value;
        return value;
    }
    function _sDelete(el, key) {
        const bucket = _shadowState.get(el);
        if (bucket) delete bucket[key];
    }

    // ─── Error reporting ──────────────────────────────────────────────────────
    const ERROR_TYPES = {
        X_FOR_SYNTAX: 'x-for-syntax',
        X_ON_UNSAFE: 'x-on-unsafe',
        X_BIND_EVAL: 'x-bind-eval',
        X_IF_EVAL: 'x-if-eval',
        RENDER_ERROR: 'render-error',
        MODEL_PATH: 'model-path',
        WATCHER_ERROR: 'watcher-error',
        LIFECYCLE: 'lifecycle-error',
        PROXY_TARGET: 'proxy-target',
        SECURITY_BLOCKED: 'security-blocked',
    };

    function _elementId(el) {
        if (!el || !el.tagName) return 'unknown';
        return el.tagName + (el.id ? '#' + el.id : '') + (el.className && typeof el.className === 'string' ? '.' + el.className.trim().split(/\s+/).join('.') : '');
    }

    function _reportError(type, message, ctx) {
        const err = Object.assign({ type: type, message: message, timestamp: Date.now() }, ctx || {});
        if (typeof shadowProxy.onError === 'function') {
            try { shadowProxy.onError(err); } catch (e) { console.error('[shadow-proxy] onError threw:', e); }
        } else {
            console.error('[shadow-proxy] ' + type + ':', message, err);
        }
    }

    // ─── Helpers de objeto ────────────────────────────────────────────────────
    // Só Array e objetos literais/null-proto são proxificados (Date, Map, Set, Blob... ficam crus).
    function _isProxyable(v) {
        if (Array.isArray(v)) return true;
        const proto = Object.getPrototypeOf(v);
        return proto === Object.prototype || proto === null;
    }

    function _allKeys(scope) {
        const ks = [];
        for (const k in scope) ks.push(k);
        return ks;
    }

    function _pick(obj, parts) {
        for (let i = 0; i < parts.length; i++) {
            if (obj == null) return undefined;
            obj = obj[parts[i]];
        }
        return obj;
    }

    // ─── Watchers ─────────────────────────────────────────────────────────────
    const _watchers = Object.create(null);
    const _modelRegistry = new Map();
    const _pendingBinds = new Map();

    function _modelRegistryAdd(key, el) {
        if (!_modelRegistry.has(key)) _modelRegistry.set(key, new Set());
        _modelRegistry.get(key).add(el);
    }
    function _modelRegistryRemove(key) { _modelRegistry.delete(key); }

    function _snapshotAncestors(path) {
        const snapshots = new Map();
        if (Object.keys(_watchers).length === 0) return snapshots;
        let idx = path.lastIndexOf('.');
        while (idx !== -1) {
            const ancestorPath = path.slice(0, idx);
            if (_watchers[ancestorPath] && _watchers[ancestorPath].size) {
                const val = _getDeep(ancestorPath.split('.'));
                let snapshot;
                if (val && typeof val === 'object') {
                    try {
                        snapshot = structuredClone(val);
                    } catch (e) {
                        try { snapshot = Object.assign(Array.isArray(val) ? [] : {}, val); }
                        catch (e2) { snapshot = val; }
                    }
                } else {
                    snapshot = val;
                }
                snapshots.set(ancestorPath, snapshot);
            }
            idx = ancestorPath.lastIndexOf('.');
        }
        return snapshots;
    }

    function _notifyWatchers(path, newVal, oldVal, ancestorSnapshots, noBubble) {
        if (newVal !== oldVal) {
            const fns = _watchers[path];
            if (fns && fns.size) {
                fns.forEach(function (fn) {
                    try { fn(newVal, oldVal); } catch (e) { _reportError(ERROR_TYPES.WATCHER_ERROR, 'Watcher threw', { path: path, message: e.message }); }
                });
            }
        }
        if (newVal === oldVal || noBubble) return;

        let idx = path.lastIndexOf('.');
        while (idx !== -1) {
            const ancestorPath = path.slice(0, idx);
            const fns = _watchers[ancestorPath];
            if (fns && fns.size) {
                const ancestorNewVal = _getDeep(ancestorPath.split('.'));
                const ancestorOldVal = ancestorSnapshots && ancestorSnapshots.has(ancestorPath)
                    ? ancestorSnapshots.get(ancestorPath)
                    : ancestorNewVal;
                fns.forEach(function (fn) {
                    try { fn(ancestorNewVal, ancestorOldVal); } catch (e) { _reportError(ERROR_TYPES.WATCHER_ERROR, 'Watcher threw', { path: ancestorPath, message: e.message }); }
                });
            }
            idx = ancestorPath.lastIndexOf('.');
        }
    }

    function _registerWatcher(path, fn) {
        if (!_watchers[path]) _watchers[path] = new Set();
        _watchers[path].add(fn);
        return function () {
            const s = _watchers[path];
            if (!s) return;
            s.delete(fn);
            if (!s.size) delete _watchers[path];
        };
    }

    // ─── Granular reactivity — track / trigger ───────────────────────────────
    const _deps = new WeakMap();
    let _activeEffect = null;

    function _track(rawObj, prop) {
        if (!_activeEffect || _activeEffect.dead) return;
        if (!_deps.has(rawObj)) _deps.set(rawObj, new Map());
        const propMap = _deps.get(rawObj);
        if (!propMap.has(prop)) propMap.set(prop, new Set());
        const effects = propMap.get(prop);
        if (!effects.has(_activeEffect)) {
            effects.add(_activeEffect);
            _activeEffect.deps.add(effects);
        }
    }

    function _hasEffects(rawObj, prop) {
        const propMap = _deps.get(rawObj);
        if (!propMap) return false;
        const effects = propMap.get(prop);
        return !!(effects && effects.size);
    }

    function _trigger(rawObj, prop) {
        if (!_hasEffects(rawObj, prop)) return false;
        _deps.get(rawObj).get(prop).forEach(function (e) { e.schedule(); });
        return true;
    }

    // ─── Effect ───────────────────────────────────────────────────────────────
    function _createEffect(fn) {
        const effect = {
            fn: fn,
            deps: new Set(),
            scheduled: false,
            dead: false,
            key: null,

            cleanup() {
                effect.deps.forEach(function (depSet) { depSet.delete(effect); });
                effect.deps.clear();
            },

            kill() {
                effect.dead = true;
                effect.cleanup();
                _pendingEffects.delete(effect);
            },

            run() {
                if (effect.dead) return;
                effect.cleanup();
                const prev = _activeEffect;
                _activeEffect = effect;
                try { fn(); } finally { _activeEffect = prev; }
            },

            schedule() {
                if (effect.dead || effect.scheduled) return;
                effect.scheduled = true;
                _pendingEffects.add(effect);
                _scheduleFlush();
            }
        };
        return effect;
    }

    // ─── Flush de effects (microtask) ────────────────────────────────────────
    const _FLUSH_MAX_GENERATIONS = 10;
    const _pendingEffects = new Set();
    let _flushQueued = false;
    let _flushDepth = 0;

    function _scheduleFlush() {
        if (_flushQueued) return;
        _flushQueued = true;
        Promise.resolve().then(function () {
            _flushQueued = false;
            _flushDepth = 0;

            while (_pendingEffects.size > 0) {
                if (_flushDepth >= _FLUSH_MAX_GENERATIONS) {
                    _reportError(ERROR_TYPES.RENDER_ERROR,
                        'Loop de reatividade detectado: ' + _FLUSH_MAX_GENERATIONS + ' gerações de effects sem estabilizar. Verifique mutations dentro de renders.',
                        { pendingCount: _pendingEffects.size }
                    );
                    _pendingEffects.forEach(function (e) { e.scheduled = false; });
                    _pendingEffects.clear();
                    break;
                }

                _flushDepth++;
                const batch = [..._pendingEffects];
                _pendingEffects.clear();

                const keysToSync = new Set();
                batch.forEach(function (e) {
                    e.scheduled = false;
                    if (e.dead) return;
                    try {
                        e.run();
                    } catch (err) {
                        _reportError(ERROR_TYPES.RENDER_ERROR, 'Effect threw durante o flush', {
                            message: err && err.message,
                            component: e.key,
                        });
                    }
                    if (e.key) keysToSync.add(e.key);
                });

                keysToSync.forEach(_syncModelsForKey);
            }

            _flushDepth = 0;
        });
    }

    // ─── Batching para _applyTarget ──────────────────────────────────────────
    const _pendingKeys = new Set();
    const _pendingKeysNeedRender = new Set();
    let _applyQueued = false;
    let _applyChain = 0;
    let _applyBlocked = false;
    const _APPLY_MAX_CHAIN = 100;

    function _scheduleApply(key, needsRender) {
        if (needsRender === undefined) needsRender = true;
        if (_forErrDeps[key]) _trigger(_forErrDeps[key], 'v');
        _pendingKeys.add(key);
        if (needsRender) _pendingKeysNeedRender.add(key);
        if (_applyQueued) return;
        _applyQueued = true;
        Promise.resolve().then(function () {
            _applyQueued = false;

            // Guard: hooks ($afterRender etc.) que mutam o store em cadeia infinita
            if (++_applyChain === 1) {
                setTimeout(function () { _applyChain = 0; _applyBlocked = false; }, 0);
            }
            if (_applyChain > _APPLY_MAX_CHAIN) {
                if (!_applyBlocked) {
                    _applyBlocked = true;
                    _reportError(ERROR_TYPES.RENDER_ERROR,
                        'Loop de render detectado: ' + _APPLY_MAX_CHAIN + ' ciclos seguidos. Verifique mutations em $afterRender/$beforeRender/watchers.',
                        { pendingCount: _pendingKeys.size });
                }
                _pendingKeys.clear();
                _pendingKeysNeedRender.clear();
                return;
            }

            const keys = [..._pendingKeys];
            const needRender = new Set(_pendingKeysNeedRender);
            _pendingKeys.clear();
            _pendingKeysNeedRender.clear();
            keys.forEach(function (k) {
                try {
                    _applyTarget(k, needRender.has(k));
                } catch (err) {
                    _reportError(ERROR_TYPES.RENDER_ERROR, '_applyTarget threw', {
                        message: err && err.message,
                        component: k,
                    });
                }
            });
            keys.forEach(_syncModelsForKey);
        });
    }

    // ─── Segurança — parser AST mínimo ───────────────────────────────────────

    const _SAFE_GLOBALS = new Set([
        'true', 'false', 'null', 'undefined', 'event', 'typeof',
        'Math', 'JSON', 'Date', 'Number', 'String', 'Boolean', 'Array', 'Object',
        'parseInt', 'parseFloat', 'isNaN', 'isFinite'
    ]);

    // Propriedades bloqueadas em QUALQUER acesso a membro (a.b / a['b'])
    const _BLOCKED_PROPS = new Set([
        'constructor', 'prototype', '__proto__', '__raw',
        '__defineGetter__', '__defineSetter__', '__lookupGetter__', '__lookupSetter__',
        'caller', 'callee', 'arguments', 'call', 'apply', 'bind',
        'getPrototypeOf', 'setPrototypeOf', 'getOwnPropertyDescriptor',
        'getOwnPropertyDescriptors', 'defineProperty', 'defineProperties',
    ]);

    // Identificadores LIVRES bloqueados (globais perigosos). Nomes ambíguos
    // (parent, top, self, location, history, open, close, process, module...)
    // só resolvem contra o scope, então são dados do usuário — liberados.
    const _BLOCKED_IDS = new Set([
        'eval', 'Function', 'fetch', 'XMLHttpRequest', 'WebSocket', 'Worker',
        'window', 'document', 'globalThis', 'global', 'navigator', 'alert', 'confirm', 'prompt',
        'setTimeout', 'setInterval', 'clearTimeout', 'clearInterval',
        'requestAnimationFrame', 'cancelAnimationFrame',
        'import', 'require',
        'Reflect', 'Proxy', 'Symbol', 'WeakMap', 'WeakSet', 'WeakRef',
        'atob', 'btoa', 'postMessage',
    ]);
    _BLOCKED_PROPS.forEach(function (p) { _BLOCKED_IDS.add(p); });

    // Propriedades de Node bloqueadas (vazam Document/Window ou injetam HTML)
    const _NODE_BLOCKED = new Set([
        'ownerDocument', 'defaultView', 'contentWindow', 'contentDocument',
        'innerHTML', 'outerHTML', 'insertAdjacentHTML', 'srcdoc', 'cookie'
    ]);

    const _TWO_CHAR_OPS = ['++', '--', '+=', '-=', '*=', '/=', '%=',
        '==', '!=', '<=', '>=', '&&', '||', '??', '=>', '**'];
    const _STR_ESCAPES = { n: '\n', t: '\t', r: '\r' };

    function _tokenize(expr) {
        const tokens = [];
        let i = 0;
        const len = expr.length;

        while (i < len) {
            if (/\s/.test(expr[i])) { i++; continue; }

            // String
            if (expr[i] === '\'' || expr[i] === '"') {
                const q = expr[i++];
                let s = '';
                while (i < len && expr[i] !== q) {
                    if (expr[i] === '\\' && i + 1 < len) {
                        i++;
                        const esc = expr[i++];
                        s += (esc in _STR_ESCAPES) ? _STR_ESCAPES[esc] : esc;
                    } else {
                        s += expr[i++];
                    }
                }
                if (expr[i] === q) i++;
                tokens.push({ type: 'str', value: s });
                continue;
            }

            // Número (um ponto decimal, expoente)
            if (/[0-9]/.test(expr[i]) || (expr[i] === '.' && /[0-9]/.test(expr[i + 1] || ''))) {
                let n = '';
                let hasDot = false;
                while (i < len) {
                    const c = expr[i];
                    if (/[0-9]/.test(c)) { n += c; i++; continue; }
                    if (c === '.' && !hasDot && /[0-9]/.test(expr[i + 1] || '')) { hasDot = true; n += c; i++; continue; }
                    break;
                }
                const m = /^[eE][+-]?[0-9]+/.exec(expr.slice(i));
                if (m) { n += m[0]; i += m[0].length; }
                tokens.push({ type: 'num', value: n });
                continue;
            }

            // Identificador (unicode)
            if (/[\p{L}_$]/u.test(expr[i])) {
                let id = '';
                while (i < len && /[\p{L}\p{N}_$]/u.test(expr[i])) id += expr[i++];
                tokens.push({ type: 'id', value: id });
                continue;
            }

            // Operadores de 3 chars
            const threeChar = expr.slice(i, i + 3);
            if (threeChar === '===' || threeChar === '!==') {
                tokens.push({ type: 'op', value: threeChar });
                i += 3;
                continue;
            }

            // Optional chaining (não confunde com ternário "a?.5:1")
            if (expr[i] === '?' && expr[i + 1] === '.' && !/[0-9]/.test(expr[i + 2] || '')) {
                tokens.push({ type: 'op', value: '?.' });
                i += 2;
                continue;
            }

            const twoChar = expr.slice(i, i + 2);
            if (_TWO_CHAR_OPS.includes(twoChar)) {
                tokens.push({ type: 'op', value: twoChar });
                i += 2;
                continue;
            }

            if ('=+-*/%!<>&|?:.,;()[]{}'.includes(expr[i])) {
                tokens.push({ type: 'punc', value: expr[i++] });
                continue;
            }

            return null;
        }

        return tokens;
    }

    // ─── Parser AST + Interpreter ────────────────────────────────────────────

    function _SecurityError(message) {
        this.name = 'SecurityError';
        this.message = message;
    }
    _SecurityError.prototype = Object.create(Error.prototype);

    function _assertSafeProp(name) {
        if (_BLOCKED_PROPS.has(name)) throw new _SecurityError('Acesso bloqueado: "' + name + '"');
    }
    function _assertSafeId(name) {
        if (_BLOCKED_IDS.has(name)) throw new _SecurityError('Acesso bloqueado: "' + name + '"');
    }

    // Nenhuma leitura pode devolver Window/Document/Function (cobre event.view,
    // getRootNode(), composedPath()[n], parentNode encadeado, etc.)
    function _guardValue(v) {
        if (v === window || v === document || v === globalThis || v === Function) {
            throw new _SecurityError('Acesso bloqueado a objeto global');
        }
        return v;
    }

    function _isNode(o) {
        return typeof Node !== 'undefined' && o instanceof Node;
    }

    const ASSIGN_OPS = new Set(['=', '+=', '-=', '*=', '/=', '%=']);

    function _Parser(tokens) {
        this.tokens = tokens;
        this.pos = 0;
    }
    _Parser.prototype.peek = function (offset) { return this.tokens[this.pos + (offset || 0)]; };
    _Parser.prototype.next = function () { return this.tokens[this.pos++]; };
    _Parser.prototype.atEnd = function () { return this.pos >= this.tokens.length; };
    _Parser.prototype.is = function (type, value) {
        const t = this.peek();
        if (!t || t.type !== type) return false;
        if (value !== undefined && t.value !== value) return false;
        return true;
    };
    _Parser.prototype.isPunc = function (v) { return this.is('punc', v); };
    _Parser.prototype.isAnyOp = function (v) {
        const t = this.peek();
        return !!t && (t.type === 'op' || t.type === 'punc') && t.value === v;
    };
    _Parser.prototype.expectPunc = function (v) {
        if (!this.isPunc(v)) throw new SyntaxError('Esperado "' + v + '"');
        return this.next();
    };
    _Parser.prototype.parseProgram = function () {
        const body = [];
        if (this.atEnd()) return { type: 'Program', body: body };
        body.push(this.parseAssignment());
        while (this.isPunc(';')) {
            this.next();
            if (this.atEnd()) break;
            body.push(this.parseAssignment());
        }
        if (!this.atEnd()) throw new SyntaxError('Token inesperado: ' + JSON.stringify(this.peek()));
        return { type: 'Program', body: body };
    };
    _Parser.prototype._assertLValue = function (node) {
        if (node.type !== 'Identifier' && node.type !== 'MemberExpression') {
            throw new SyntaxError('Alvo de atribuição inválido');
        }
    };
    _Parser.prototype.parseAssignment = function () {
        const left = this.parseConditional();
        const t = this.peek();
        if (t && (t.type === 'op' || t.type === 'punc') && ASSIGN_OPS.has(t.value)) {
            this.next();
            const right = this.parseAssignment();
            this._assertLValue(left);
            return { type: 'AssignmentExpression', operator: t.value, left: left, right: right };
        }
        return left;
    };
    _Parser.prototype.parseConditional = function () {
        const test = this.parseNullish();
        if (this.isPunc('?')) {
            this.next();
            const consequent = this.parseAssignment();
            this.expectPunc(':');
            const alternate = this.parseAssignment();
            return { type: 'ConditionalExpression', test: test, consequent: consequent, alternate: alternate };
        }
        return test;
    };
    _Parser.prototype.parseNullish = function () { return this._parseLogical('??', this.parseOr.bind(this)); };
    _Parser.prototype.parseOr = function () { return this._parseLogical('||', this.parseAnd.bind(this)); };
    _Parser.prototype.parseAnd = function () { return this._parseLogical('&&', this.parseEquality.bind(this)); };
    _Parser.prototype._parseLogical = function (op, nextFn) {
        let left = nextFn();
        while (this.isAnyOp(op)) {
            this.next();
            const right = nextFn();
            left = { type: 'LogicalExpression', operator: op, left: left, right: right };
        }
        return left;
    };
    _Parser.prototype.parseEquality = function () { return this._parseBinaryLevel(['==', '!=', '===', '!=='], this.parseRelational.bind(this)); };
    _Parser.prototype.parseRelational = function () { return this._parseBinaryLevel(['<', '>', '<=', '>='], this.parseAdditive.bind(this)); };
    _Parser.prototype.parseAdditive = function () { return this._parseBinaryLevel(['+', '-'], this.parseMultiplicative.bind(this)); };
    _Parser.prototype.parseMultiplicative = function () { return this._parseBinaryLevel(['*', '/', '%'], this.parseExponent.bind(this)); };
    _Parser.prototype.parseExponent = function () {
        const left = this.parseUnary();
        if (this.isAnyOp('**')) {
            this.next();
            const right = this.parseExponent();
            return { type: 'BinaryExpression', operator: '**', left: left, right: right };
        }
        return left;
    };
    _Parser.prototype._parseBinaryLevel = function (ops, nextFn) {
        let left = nextFn();
        for (; ;) {
            const t = this.peek();
            if (!t || (t.type !== 'op' && t.type !== 'punc') || ops.indexOf(t.value) === -1) break;
            this.next();
            const right = nextFn();
            left = { type: 'BinaryExpression', operator: t.value, left: left, right: right };
        }
        return left;
    };
    _Parser.prototype.parseUnary = function () {
        const t = this.peek();
        if (t && t.type === 'id' && t.value === 'typeof') {
            this.next();
            return { type: 'UnaryExpression', operator: 'typeof', argument: this.parseUnary() };
        }
        if (t && (t.type === 'punc' || t.type === 'op') && ['!', '-', '+'].indexOf(t.value) !== -1) {
            this.next();
            return { type: 'UnaryExpression', operator: t.value, argument: this.parseUnary() };
        }
        if (t && t.type === 'op' && (t.value === '++' || t.value === '--')) {
            this.next();
            const argument = this.parseUnary();
            this._assertLValue(argument);
            return { type: 'UpdateExpression', operator: t.value, argument: argument, prefix: true };
        }
        return this.parseUpdatePostfix();
    };
    _Parser.prototype.parseUpdatePostfix = function () {
        let node = this.parseCallMember();
        const t = this.peek();
        if (t && t.type === 'op' && (t.value === '++' || t.value === '--')) {
            this.next();
            this._assertLValue(node);
            node = { type: 'UpdateExpression', operator: t.value, argument: node, prefix: false };
        }
        return node;
    };
    _Parser.prototype._parseArgs = function () {
        const args = [];
        if (!this.isPunc(')')) {
            args.push(this.parseAssignment());
            while (this.isPunc(',')) { this.next(); args.push(this.parseAssignment()); }
        }
        this.expectPunc(')');
        return args;
    };
    _Parser.prototype.parseCallMember = function () {
        let node = this.parsePrimary();
        for (; ;) {
            if (this.is('op', '?.')) {
                this.next();
                if (this.isPunc('(')) {
                    this.next();
                    node = { type: 'CallExpression', callee: node, arguments: this._parseArgs(), optional: true };
                } else if (this.isPunc('[')) {
                    this.next();
                    const property = this.parseAssignment();
                    this.expectPunc(']');
                    node = { type: 'MemberExpression', object: node, property: property, computed: true, optional: true };
                } else {
                    const prop = this.next();
                    if (!prop || prop.type !== 'id') throw new SyntaxError('Esperado identificador após "?."');
                    node = { type: 'MemberExpression', object: node, property: { type: 'Identifier', name: prop.value }, computed: false, optional: true };
                }
            } else if (this.isPunc('.')) {
                this.next();
                const prop = this.next();
                if (!prop || prop.type !== 'id') throw new SyntaxError('Esperado identificador após "."');
                node = { type: 'MemberExpression', object: node, property: { type: 'Identifier', name: prop.value }, computed: false };
            } else if (this.isPunc('[')) {
                this.next();
                const property = this.parseAssignment();
                this.expectPunc(']');
                node = { type: 'MemberExpression', object: node, property: property, computed: true };
            } else if (this.isPunc('(')) {
                this.next();
                node = { type: 'CallExpression', callee: node, arguments: this._parseArgs() };
            } else break;
        }
        return node;
    };
    _Parser.prototype.parsePrimary = function () {
        const t = this.peek();
        if (!t) throw new SyntaxError('Fim inesperado da expressão');
        if (t.type === 'num') { this.next(); return { type: 'Literal', value: parseFloat(t.value) }; }
        if (t.type === 'str') { this.next(); return { type: 'Literal', value: t.value }; }
        if (t.type === 'id') {
            this.next();
            if (t.value === 'true') return { type: 'Literal', value: true };
            if (t.value === 'false') return { type: 'Literal', value: false };
            if (t.value === 'null') return { type: 'Literal', value: null };
            if (t.value === 'undefined') return { type: 'Literal', value: undefined };
            return { type: 'Identifier', name: t.value };
        }
        if (this.isPunc('(')) {
            this.next();
            const expr = this.parseAssignment();
            this.expectPunc(')');
            return expr;
        }
        if (this.isPunc('[')) {
            this.next();
            const elements = [];
            if (!this.isPunc(']')) {
                elements.push(this.parseAssignment());
                while (this.isPunc(',')) { this.next(); elements.push(this.parseAssignment()); }
            }
            this.expectPunc(']');
            return { type: 'ArrayExpression', elements: elements };
        }
        if (this.isPunc('{')) {
            this.next();
            const properties = [];
            if (!this.isPunc('}')) {
                for (; ;) {
                    const keyTok = this.next();
                    if (!keyTok || (keyTok.type !== 'id' && keyTok.type !== 'str')) throw new SyntaxError('Chave de objeto inválida');
                    this.expectPunc(':');
                    const value = this.parseAssignment();
                    properties.push({ key: String(keyTok.value), value: value });
                    if (this.isPunc(',')) { this.next(); continue; }
                    break;
                }
            }
            this.expectPunc('}');
            return { type: 'ObjectExpression', properties: properties };
        }
        throw new SyntaxError('Token inesperado: ' + JSON.stringify(t));
    };

    function _parseAST(expr) {
        const tokens = _tokenize(expr);
        if (!tokens) throw new SyntaxError('Falha na tokenização');
        return new _Parser(tokens).parseProgram();
    }

    const _AST_CACHE_MAX = 500;
    const _astCache = new Map();
    function _getAST(expr) {
        let ast = _astCache.get(expr);
        if (ast) { _astCache.delete(expr); _astCache.set(expr, ast); return ast; }
        ast = _parseAST(expr);
        if (_astCache.size >= _AST_CACHE_MAX) _astCache.delete(_astCache.keys().next().value);
        _astCache.set(expr, ast);
        return ast;
    }

    const _INTERP_SAFE_GLOBALS = {
        Math: Math, JSON: JSON, Date: Date, Number: Number, String: String,
        Boolean: Boolean, Array: Array, Object: Object,
        parseInt: parseInt, parseFloat: parseFloat, isNaN: isNaN, isFinite: isFinite,
    };
    const _SAFE_OBJS = Object.keys(_INTERP_SAFE_GLOBALS).map(function (k) { return _INTERP_SAFE_GLOBALS[k]; });

    // lenient=true (render): identificador inexistente → undefined (e ainda rastreia a dependência).
    // lenient=false (x-on): lança ReferenceError.
    function _Interpreter(scope, lenient) { this.scope = scope; this.lenient = !!lenient; }
    _Interpreter.prototype.run = function (ast) {
        let result;
        for (let i = 0; i < ast.body.length; i++) result = this.evalNode(ast.body[i]);
        return result;
    };
    _Interpreter.prototype._checkNodeCall = function (obj, key, args) {
        if (!_isNode(obj)) return;
        const k = String(key);
        if (k === 'setAttribute' || k === 'setAttributeNS') {
            const name = String(k === 'setAttribute' ? args[0] : args[1]);
            if (/^(on|src|href|action|formaction|srcdoc|xlink)/i.test(name)) {
                throw new _SecurityError('setAttribute bloqueado: "' + name + '"');
            }
        }
    };
    _Interpreter.prototype.evalNode = function (node) {
        switch (node.type) {
            case 'Literal': return node.value;
            case 'Identifier': {
                const name = node.name;
                if (Object.prototype.hasOwnProperty.call(_INTERP_SAFE_GLOBALS, name)) return _INTERP_SAFE_GLOBALS[name];
                _assertSafeId(name);
                const v = this.scope[name];   // leitura sempre acontece → rastreia dependência
                if (v === undefined && !(name in this.scope)) {
                    if (this.lenient) return undefined;
                    throw new ReferenceError('"' + name + '" não existe no scope');
                }
                return _guardValue(v);
            }
            case 'ArrayExpression':
                return node.elements.map(function (el) { return this.evalNode(el); }, this);
            case 'ObjectExpression': {
                const obj = {};
                for (let i = 0; i < node.properties.length; i++) {
                    const p = node.properties[i];
                    _assertSafeProp(p.key);
                    obj[p.key] = this.evalNode(p.value);
                }
                return obj;
            }
            case 'MemberExpression': {
                const r = this._resolveMember(node);
                return r.obj == null ? undefined : _guardValue(r.obj[r.key]);
            }
            case 'CallExpression': {
                if (node.callee.type === 'MemberExpression') {
                    const r = this._resolveMember(node.callee);
                    if (r.obj == null) {
                        if (node.callee.optional || node.optional) return undefined;
                        throw new TypeError('Chamando método em null/undefined');
                    }
                    const fn = r.obj[r.key];
                    if (fn == null && node.optional) return undefined;
                    if (typeof fn !== 'function') throw new TypeError('"' + String(r.key) + '" não é função');
                    const args = node.arguments.map(function (a) { return this.evalNode(a); }, this);
                    this._checkNodeCall(r.obj, r.key, args);
                    return _guardValue(fn.apply(r.obj, args));
                }
                if (node.callee.type === 'Identifier') {
                    const fn = this.evalNode(node.callee);
                    if (fn == null && node.optional) return undefined;
                    if (typeof fn !== 'function') throw new TypeError('"' + node.callee.name + '" não é função');
                    const args = node.arguments.map(function (a) { return this.evalNode(a); }, this);
                    return _guardValue(fn.apply(null, args));
                }
                throw new _SecurityError('Chamada não suportada');
            }
            case 'UnaryExpression': {
                if (node.operator === 'typeof') {
                    const a = node.argument;
                    if (a.type === 'Identifier' &&
                        !Object.prototype.hasOwnProperty.call(_INTERP_SAFE_GLOBALS, a.name) &&
                        !(a.name in this.scope)) return 'undefined';
                    return typeof this.evalNode(a);
                }
                const v = this.evalNode(node.argument);
                if (node.operator === '!') return !v;
                if (node.operator === '-') return -v;
                if (node.operator === '+') return +v;
                break;
            }
            case 'UpdateExpression': {
                const lv = this._resolveLValue(node.argument);
                const old = lv.isIdentifier ? this.scope[lv.key] : lv.obj[lv.key];
                const nextVal = node.operator === '++' ? old + 1 : old - 1;
                if (lv.isIdentifier) this.scope[lv.key] = nextVal; else lv.obj[lv.key] = nextVal;
                return node.prefix ? nextVal : old;
            }
            case 'BinaryExpression': {
                const l = this.evalNode(node.left), r = this.evalNode(node.right);
                switch (node.operator) {
                    case '+': return l + r;
                    case '-': return l - r;
                    case '*': return l * r;
                    case '/': return l / r;
                    case '%': return l % r;
                    case '**': return Math.pow(l, r);
                    case '==': return l == r;
                    case '!=': return l != r;
                    case '===': return l === r;
                    case '!==': return l !== r;
                    case '<': return l < r;
                    case '>': return l > r;
                    case '<=': return l <= r;
                    case '>=': return l >= r;
                }
                break;
            }
            case 'LogicalExpression': {
                const l = this.evalNode(node.left);
                if (node.operator === '&&') return l ? this.evalNode(node.right) : l;
                if (node.operator === '||') return l ? l : this.evalNode(node.right);
                if (node.operator === '??') return l != null ? l : this.evalNode(node.right);
                break;
            }
            case 'ConditionalExpression':
                return this.evalNode(node.test) ? this.evalNode(node.consequent) : this.evalNode(node.alternate);
            case 'AssignmentExpression': {
                const lv = this._resolveLValue(node.left);
                let value = this.evalNode(node.right);
                if (node.operator !== '=') {
                    const current = lv.isIdentifier ? this.scope[lv.key] : lv.obj[lv.key];
                    switch (node.operator) {
                        case '+=': value = current + value; break;
                        case '-=': value = current - value; break;
                        case '*=': value = current * value; break;
                        case '/=': value = current / value; break;
                        case '%=': value = current % value; break;
                    }
                }
                if (lv.isIdentifier) this.scope[lv.key] = value; else lv.obj[lv.key] = value;
                return value;
            }
            default:
                throw new _SecurityError('Nó não suportado: ' + node.type);
        }
    };
    _Interpreter.prototype._resolveMember = function (node) {
        const obj = this.evalNode(node.object);
        const key = node.computed ? this.evalNode(node.property) : node.property.name;
        const skey = typeof key === 'symbol' ? '' : String(key);
        _assertSafeProp(skey);
        if (obj != null && _isNode(obj) && _NODE_BLOCKED.has(skey)) {
            throw new _SecurityError('Acesso bloqueado: "' + skey + '"');
        }
        return { obj: obj, key: key };
    };
    _Interpreter.prototype._resolveLValue = function (node) {
        if (node.type === 'Identifier') {
            _assertSafeId(node.name);
            return { key: node.name, isIdentifier: true };
        }
        const r = this._resolveMember(node);
        if (r.obj != null) {
            if (_SAFE_OBJS.indexOf(r.obj) !== -1) throw new _SecurityError('Escrita bloqueada em global');
            if (_isNode(r.obj) && /^on/i.test(String(r.key))) throw new _SecurityError('Escrita bloqueada: "' + String(r.key) + '"');
        }
        return { obj: r.obj, key: r.key, isIdentifier: false };
    };

    // Heurística de bind (bind agora x aguardar prop existir) — NÃO é a fronteira de segurança.
    function _validateTokens(tokens, scopeKeys) {
        if (!tokens) return false;
        let braceDepth = 0;

        for (let i = 0; i < tokens.length; i++) {
            const tok = tokens[i];

            if (tok.type === 'punc' && tok.value === '{') { braceDepth++; continue; }
            if (tok.type === 'punc' && tok.value === '}') { braceDepth = Math.max(0, braceDepth - 1); continue; }
            if (tok.type === 'op' && tok.value === '=>') return false;
            if (tok.type !== 'id') continue;

            const prev = tokens[i - 1];
            if (prev && ((prev.type === 'punc' && prev.value === '.') || (prev.type === 'op' && prev.value === '?.'))) continue;

            if (_BLOCKED_IDS.has(tok.value)) return false;

            const next = tokens[i + 1];
            if (braceDepth > 0 && next && next.type === 'punc' && next.value === ':') continue;
            if (next && next.type === 'punc' && next.value === '=') continue;
            if (_SAFE_GLOBALS.has(tok.value)) continue;
            if (scopeKeys.has(tok.value)) continue;

            return false;
        }
        return true;
    }

    function _safeExpr(expr, scopeKeys) {
        const trimmed = expr.trim();
        if (!trimmed) return false;
        return _validateTokens(_tokenize(trimmed), scopeKeys || new Set());
    }

    function _isBlockedExpr(expr) {
        const tokens = _tokenize(expr.trim());
        if (!tokens) return true;
        return tokens.some(function (tok, i) {
            if (tok.type === 'op' && tok.value === '=>') return true;
            if (tok.type !== 'id') return false;
            const prev = tokens[i - 1];
            if (prev && ((prev.type === 'punc' && prev.value === '.') || (prev.type === 'op' && prev.value === '?.'))) return false;
            return _BLOCKED_IDS.has(tok.value);
        });
    }

    function _evalExpr(expr, scope, componentKey, errType) {
        try {
            const ast = _getAST(expr);
            return new _Interpreter(scope, true).run(ast);
        } catch (e) {
            const type = (e instanceof _SecurityError) ? ERROR_TYPES.SECURITY_BLOCKED : (errType || ERROR_TYPES.X_BIND_EVAL);
            _reportError(type, 'Falha ao avaliar expressão', {
                expr: expr,
                message: e.message,
                component: componentKey,
            });
            return undefined;
        }
    }

    // "{...}" que não é expressão válida (pattern="\d{3}", JSON) é preservado como texto.
    function _interpolate(str, scope, componentKey) {
        return str.replace(/\{([^}]+)\}/g, function (match, expr) {
            const e = expr.trim();
            if (/^\d+\s*(,\s*\d*)?$/.test(e)) return match;     // quantificador regex {3} {2,5}
            try { _getAST(e); } catch (err) { return match; }   // não é expressão
            const val = _evalExpr(e, scope, componentKey);
            return val != null ? val : '';
        });
    }

    function _isTruthy(expr, scope, componentKey) {
        return !!_evalExpr(expr, scope, componentKey, ERROR_TYPES.X_IF_EVAL);
    }

    // ─── Sanitização de atributos interpolados ───────────────────────────────
    const _URL_ATTRS = new Set(['href', 'src', 'action', 'formaction', 'xlink:href', 'data', 'poster', 'srcset']);

    function _isUnsafeUrl(value) {
        const s = String(value).replace(/[\u0000-\u0020\u007f-\u009f]+/g, '').toLowerCase();
        return /^(javascript|vbscript|data:text\/html)/.test(s);
    }

    const _BOOL_ATTRS = new Set(['disabled', 'checked', 'selected', 'readonly', 'required', 'hidden', 'multiple',
        'autofocus', 'open', 'async', 'defer', 'novalidate', 'autoplay', 'controls', 'loop', 'muted', 'reversed', 'inert']);
    const _BOOL_PROPS = { readonly: 'readOnly', novalidate: 'noValidate' };

    // ─── x-model ──────────────────────────────────────────────────────────────

    function _parsePath(path) {
        const parts = path.replace(/\[(\d+)\]/g, '.$1').split('.');
        return { key: parts[0], parts: parts };
    }

    function _unsafePath(parts) {
        return parts.some(function (p) { return _BLOCKED_PROPS.has(p); });
    }

    function _setDeep(parts, value) {
        if (_unsafePath(parts)) {
            _reportError(ERROR_TYPES.MODEL_PATH, 'Caminho bloqueado no x-model', { path: parts.join('.') });
            return;
        }
        if (!_proxies[parts[0]]) {
            if (!_store[parts[0]]) _store[parts[0]] = {};
            _proxies[parts[0]] = _makeProxy(_store[parts[0]], parts[0]);
        }

        let obj = _proxies[parts[0]];
        for (let i = 1; i < parts.length - 1; i++) {
            obj = obj[parts[i]];
            if (obj == null) {
                _reportError(ERROR_TYPES.MODEL_PATH, 'Caminho inexistente no x-model', { path: parts.join('.') });
                return;
            }
        }
        obj[parts[parts.length - 1]] = value;
    }

    function _getDeep(parts) {
        let obj = _store;
        for (let i = 0; i < parts.length; i++) {
            if (obj == null) return undefined;
            obj = obj[parts[i]];
        }
        return obj;
    }

    function _resolveModel(el, forcedKey) {
        const { parts } = _parsePath(el.getAttribute('x-model'));
        let key = forcedKey;
        if (!key) {
            const container = el.closest('[x-data],[proxy-target]');
            if (!container) return { key: parts[0], parts: parts };
            key = container.getAttribute('x-data') || container.getAttribute('proxy-target');
        }
        const fullParts = parts[0] === key ? parts : [key].concat(parts);
        return { key: key, parts: fullParts };
    }

    function _readModelValue(el) {
        if (el.type === 'checkbox') return el.checked;
        if (el.tagName === 'SELECT' && el.multiple) {
            return Array.from(el.selectedOptions).map(function (o) { return o.value; });
        }
        if ((el.type === 'number' || el.type === 'range') && el.value !== '') {
            const n = Number(el.value);
            return isNaN(n) ? el.value : n;
        }
        return el.value;
    }

    function _applyModelValue(el, v) {
        if (el.type === 'checkbox') {
            el.checked = !!v;
        } else if (el.type === 'radio') {
            el.checked = (el.value === String(v));
        } else if (el.tagName === 'SELECT' && el.multiple) {
            const arr = Array.isArray(v) ? Array.prototype.map.call(v, String) : [];
            Array.from(el.options).forEach(function (o) { o.selected = arr.indexOf(o.value) !== -1; });
        } else {
            const str = v == null ? '' : String(v);
            if (el.value !== str) el.value = str;
        }
    }

    function _syncModelsForKey(key) {
        const els = _modelRegistry.get(key);
        if (!els || !els.size) return;
        els.forEach(function (el) {
            if (!el.isConnected) { els.delete(el); return; }
            const parts = _sGet(el, 'modelParts');
            if (parts) _applyModelValue(el, _getDeep(parts));
        });
    }

    function _bindStoreModel(el, forcedKey) {
        if (_sGet(el, 'model')) return;

        const { key, parts } = _resolveModel(el, forcedKey);
        if (_unsafePath(parts)) {
            _reportError(ERROR_TYPES.MODEL_PATH, 'Caminho bloqueado no x-model', { path: parts.join('.'), element: _elementId(el) });
            return;
        }
        _sSet(el, 'model', true);
        _sSet(el, 'modelParts', parts);

        if (!_store[parts[0]]) _store[parts[0]] = {};
        if (!_proxies[parts[0]]) _proxies[parts[0]] = _makeProxy(_store[parts[0]], parts[0]);

        const effect = _createEffect(function () {
            let obj = _proxies[parts[0]];
            for (let i = 1; i < parts.length - 1; i++) {
                if (obj == null) return;
                obj = obj[parts[i]];
            }
            const v = obj == null ? undefined : obj[parts[parts.length - 1]];
            _applyModelValue(el, v);
        });
        effect.key = key;
        _sSet(el, 'modelEffect', effect);
        effect.run();

        _modelRegistryAdd(key, el);

        function _onInput() { _setDeep(parts, _readModelValue(el)); }

        _sSet(el, 'modelHandler', _onInput);
        el.addEventListener('input', _onInput);
        el.addEventListener('change', _onInput);
    }

    function _initModels(root) {
        const _root = (root && root.nodeType === Node.ELEMENT_NODE) ? root : document;
        _root.querySelectorAll('[x-model]').forEach(function (el) {
            if (_sGet(el, 'model') || _sGet(el, 'loopModel')) return;
            if (el.closest('[x-for]')) return;   // dentro de x-for → _bindModelsInLoop
            _bindStoreModel(el);
        });
    }

    // x-model dentro de x-for: alias do loop → bind direto no proxy do item;
    // qualquer outro path → model normal do store (com a key do componente).
    function _bindModelsInLoop(root, scope, rootKey) {
        if (!root || root.nodeType !== Node.ELEMENT_NODE) return;
        const candidates = root.hasAttribute('x-model')
            ? [root].concat(Array.from(root.querySelectorAll('[x-model]')))
            : Array.from(root.querySelectorAll('[x-model]'));

        candidates.forEach(function (el) {
            if (el !== root && _isScopedAway(el, root)) return;   // pertence a x-for/x-data aninhado

            const { parts } = _parsePath(el.getAttribute('x-model'));
            const locals = scope[_SCOPE_VARS] || [];

            if (locals.indexOf(parts[0]) === -1) {
                if (rootKey) _bindStoreModel(el, rootKey);
                return;
            }

            const aliasVal = scope[parts[0]];
            const subParts = parts.slice(1);
            if (!aliasVal || typeof aliasVal !== 'object' || !aliasVal[_PROXY_SYM] || !subParts.length) return;
            if (_unsafePath(subParts)) {
                _reportError(ERROR_TYPES.MODEL_PATH, 'Caminho bloqueado no x-model', { path: parts.join('.'), element: _elementId(el) });
                return;
            }

            if (_sGet(el, 'loopModel')) {
                _sSet(el, 'loopAlias', aliasVal);
                const existingEffect = _sGet(el, 'loopModelEffect');
                if (existingEffect) existingEffect.run();
                return;
            }
            _sSet(el, 'loopModel', true);
            _sSet(el, 'loopAlias', aliasVal);

            function _getVal() {
                let obj = _sGet(el, 'loopAlias');
                for (let i = 0; i < subParts.length - 1; i++) {
                    if (obj == null) return undefined;
                    obj = obj[subParts[i]];
                }
                return obj == null ? undefined : obj[subParts[subParts.length - 1]];
            }
            function _setVal(v) {
                let obj = _sGet(el, 'loopAlias');
                for (let i = 0; i < subParts.length - 1; i++) {
                    if (obj == null) return;
                    obj = obj[subParts[i]];
                }
                if (obj != null) obj[subParts[subParts.length - 1]] = v;
            }

            const effect = _createEffect(function () { _applyModelValue(el, _getVal()); });
            effect.key = rootKey;
            _sSet(el, 'loopModelEffect', effect);
            effect.run();

            function _onInput() { _setVal(_readModelValue(el)); }
            _sSet(el, 'loopModelHandler', _onInput);
            el.addEventListener('input', _onInput);
            el.addEventListener('change', _onInput);
        });
    }

    // ─── x-on ─────────────────────────────────────────────────────────────────

    // true se o elemento pertence a outro x-for ou a outro x-data/proxy-target aninhado
    // (excluindo o próprio root) — esses são tratados pelo seu próprio render.
    function _isScopedAway(el, root) {
        let a = el.parentElement;
        while (a && a !== root) {
            if (a.hasAttribute('x-for') || a.hasAttribute('x-data') || a.hasAttribute('proxy-target')) return true;
            a = a.parentElement;
        }
        return false;
    }

    function _bindEvents(root, scope, key) {
        if (!root || root.nodeType !== Node.ELEMENT_NODE) return;
        const els = [root].concat(Array.from(root.querySelectorAll('*')));

        els.forEach(function (el) {
            if (!el.attributes) return;
            if (el !== root && _isScopedAway(el, root)) return;

            Array.from(el.attributes).forEach(function (attr) {
                if (!attr.name.startsWith('x-on:')) return;
                const event = attr.name.slice(5);
                const expr = attr.value;
                const sKey = 'on_' + event;
                const scopeKey = 'evScope_' + event;

                // Já bindado — só atualiza o scope
                if (_sGet(el, sKey)) {
                    _sSet(el, scopeKey, scope);
                    return;
                }

                const validationKeys = new Set(_allKeys(scope));
                if (key && _store[key]) Object.keys(_store[key]).forEach(function (k) { validationKeys.add(k); });

                if (!_safeExpr(expr, validationKeys)) {
                    if (_isBlockedExpr(expr)) {
                        _reportError(ERROR_TYPES.X_ON_UNSAFE, 'Expressão bloqueada por segurança no x-on', {
                            expr: expr,
                            element: _elementId(el),
                            attr: attr.name,
                        });
                    } else if (key) {
                        if (!_pendingBinds.has(key)) _pendingBinds.set(key, new Set());
                        _pendingBinds.get(key).add({ el: el, scope: scope, key: key });
                    }
                    return;
                }

                _sSet(el, scopeKey, scope);

                const handler = function (e) {
                    try {
                        const curScope = _sGet(el, scopeKey) || scope;
                        const liveProxy = key ? (_proxies[key] || {}) : {};
                        const locals = new Set(curScope[_SCOPE_VARS] || []);
                        const $s = Object.create(null);

                        // Variáveis do loop/contexto vencem o store; o resto vem do proxy vivo.
                        _allKeys(curScope).forEach(function (k) {
                            if (locals.has(k) || !(k in liveProxy)) {
                                Object.defineProperty($s, k, {
                                    configurable: true, enumerable: true,
                                    get() { return curScope[k]; },
                                    set(val) { curScope[k] = val; }
                                });
                            } else {
                                Object.defineProperty($s, k, {
                                    configurable: true, enumerable: true,
                                    get() { return liveProxy[k]; },
                                    set(val) { liveProxy[k] = val; }
                                });
                            }
                        });

                        Object.keys(liveProxy).forEach(function (k) {
                            if (k in $s) return;
                            Object.defineProperty($s, k, {
                                configurable: true, enumerable: true,
                                get() { return liveProxy[k]; },
                                set(val) { liveProxy[k] = val; }
                            });
                        });

                        // Alvos de atribuição NOVA (ex: "out = ...")
                        const exprTokens = _tokenize(expr);
                        if (exprTokens) {
                            exprTokens.forEach(function (tok, i) {
                                if (tok.type !== 'id' || tok.value in $s) return;
                                const prevTok = exprTokens[i - 1];
                                if (prevTok && ((prevTok.type === 'punc' && prevTok.value === '.') || (prevTok.type === 'op' && prevTok.value === '?.'))) return;
                                const nextTok = exprTokens[i + 1];
                                if (!(nextTok && nextTok.type === 'punc' && nextTok.value === '=')) return;
                                const propName = tok.value;
                                Object.defineProperty($s, propName, {
                                    configurable: true, enumerable: true,
                                    get() { return liveProxy[propName]; },
                                    set(val) { liveProxy[propName] = val; }
                                });
                            });
                        }

                        if (!('event' in $s)) $s.event = e;

                        new _Interpreter($s, false).run(_getAST(expr));
                    } catch (err) {
                        const type = (err instanceof _SecurityError) ? ERROR_TYPES.SECURITY_BLOCKED : ERROR_TYPES.X_ON_UNSAFE;
                        _reportError(type, 'Erro ao executar x-on', {
                            expr: expr,
                            element: _elementId(el),
                            message: err.message,
                        });
                    }
                };
                _sSet(el, sKey, handler);
                el.addEventListener(event, handler);
            });
        });
    }

    // ─── Render com tracking ──────────────────────────────────────────────────

    function _renderTracked(node, scope, key) {
        const existing = _sGet(node, 'effect');
        if (existing && !existing.dead) {
            existing.scope = scope;
            if (key) existing.key = key;
            existing.run();
            return;
        }

        const effect = _createEffect(function () {
            _renderNodeRaw(node, effect.scope);
        });
        effect.scope = scope;
        effect.key = key || null;
        _sSet(node, 'effect', effect);
        effect.run();
    }

    const _SKIP_ATTRS = /^(x-bind|x-if|x-for|x-model|x-on:|x-ref|x-key|x-static|x-cloak|x-data)/;

    function _renderNodeRaw(node, scope, componentKey) {
        if (node.nodeType === Node.TEXT_NODE) return;

        const _nodeEffect = _sGet(node, 'effect');
        const ck = componentKey || (_nodeEffect && _nodeEffect.key) || null;

        const xFor = node.getAttribute && node.getAttribute('x-for');
        const xIf = node.getAttribute && node.getAttribute('x-if');
        const xBind = node.getAttribute && node.getAttribute('x-bind');

        if (xIf != null) {
            const show = _isTruthy(xIf, scope, ck);
            node.style.display = show ? '' : 'none';
            if (!show) return;
        }

        if (xBind != null) {
            if (xBind.includes('{')) {
                node.textContent = _interpolate(xBind, scope, ck);
            } else {
                const val = _evalExpr(xBind, scope, ck);
                node.textContent = val != null ? val : '';
            }
        }

        if (node.attributes) {
            let attrTpl = _sGet(node, 'attrTpl');
            if (!attrTpl) attrTpl = _sSet(node, 'attrTpl', Object.create(null));

            // 1) registra templates ORIGINAIS na primeira vez que o atributo é visto
            Array.from(node.attributes).forEach(function (attr) {
                if (_SKIP_ATTRS.test(attr.name) || (attr.name in attrTpl)) return;
                if (attr.value.indexOf('{') === -1) return;

                if (/^on/i.test(attr.name) || attr.name.toLowerCase() === 'srcdoc') {
                    attrTpl[attr.name] = null;
                    _reportError(ERROR_TYPES.SECURITY_BLOCKED, 'Interpolação em atributo bloqueada', {
                        element: _elementId(node),
                        attr: attr.name,
                    });
                    return;
                }
                attrTpl[attr.name] = attr.value;
            });

            // 2) avalia a partir dos templates (atributos booleanos removidos continuam sendo reavaliados)
            Object.keys(attrTpl).forEach(function (name) {
                const tpl = attrTpl[name];
                if (tpl === null) return;
                const lname = name.toLowerCase();

                const single = _BOOL_ATTRS.has(lname) ? tpl.match(/^\s*\{([^{}]+)\}\s*$/) : null;
                if (single) {
                    const v = _evalExpr(single[1].trim(), scope, ck);
                    const on = !!v && v !== 'false';
                    if (on) { if (node.getAttribute(name) !== '') node.setAttribute(name, ''); }
                    else node.removeAttribute(name);
                    const prop = _BOOL_PROPS[lname] || lname;
                    try { if (prop in node) node[prop] = on; } catch (e) { /* ignore */ }
                    return;
                }

                let value = _interpolate(tpl, scope, ck);

                if (_URL_ATTRS.has(lname) && _isUnsafeUrl(value)) {
                    _reportError(ERROR_TYPES.SECURITY_BLOCKED, 'URL insegura bloqueada em atributo', {
                        element: _elementId(node),
                        attr: name,
                        value: value,
                    });
                    value = 'about:blank';
                }

                if (node.getAttribute(name) !== value) node.setAttribute(name, value);
                if (lname === 'value' && 'value' in node && node.value !== value) {
                    try { node.value = value; } catch (e) { /* ignore */ }
                }
            });
        }

        if (xFor != null) {
            _renderFor(node, scope, xFor);
            return;
        }

        for (let child of node.children) {
            // x-data / proxy-target aninhado é renderizado pelo próprio componente
            if (child.hasAttribute('x-data') || child.hasAttribute('proxy-target')) continue;

            const hasDirective = child.hasAttribute('x-bind') ||
                child.hasAttribute('x-if') ||
                child.hasAttribute('x-for');

            if (hasDirective) {
                let rootKey = ck;
                if (!rootKey) {
                    let ancestor = node;
                    while (ancestor) {
                        const ancestorEffect = _sGet(ancestor, 'effect');
                        if (ancestorEffect && ancestorEffect.key) {
                            rootKey = ancestorEffect.key;
                            break;
                        }
                        ancestor = ancestor.parentElement;
                    }
                }
                _renderTracked(child, scope, rootKey);
            } else {
                _renderNodeRaw(child, scope, ck);
            }
        }
    }

    // ─── x-key / nid ──────────────────────────────────────────────────────────
    let _nidCounter = 0;
    const _nids = new WeakMap();

    function _getItemKey(item, xKeyExpr, scope) {
        if (xKeyExpr) {
            const val = _evalExpr(xKeyExpr, scope);
            if (val != null) return String(val);
        }
        if (item === null || typeof item !== 'object') return 'prim_' + String(item);
        const raw = item[_PROXY_SYM] ? item.__raw : item;
        let nid = _nids.get(raw);
        if (!nid) {
            nid = 'nid_' + (++_nidCounter);
            _nids.set(raw, nid);
        }
        return nid;
    }

    // ─── x-for ────────────────────────────────────────────────────────────────

    const _WRAPPER_MAP = {
        SELECT: 'select',
        TBODY: 'tbody',
        THEAD: 'thead',
        TFOOT: 'tfoot',
        TR: 'tr',
        UL: 'ul',
        OL: 'ol',
        DL: 'dl',
    };
    const _SVG_NS = 'http://www.w3.org/2000/svg';

    function _createWrapper(node) {
        if (node.namespaceURI === _SVG_NS) return document.createElementNS(_SVG_NS, 'g');
        return document.createElement(_WRAPPER_MAP[node.tagName] || 'div');
    }

    const _ID = '[\\p{L}_$][\\p{L}\\p{N}_$]*';
    const _FOR_AS = new RegExp('^\\s*(' + _ID + ')\\s+in\\s+(.+?)\\s+as\\s+(' + _ID + ')\\s*$', 'u');
    const _FOR_COMMA = new RegExp('^\\s*(' + _ID + ')\\s*,\\s*(' + _ID + ')\\s+in\\s+(.+)\\s*$', 'u');
    const _FOR_PLAIN = new RegExp('^\\s*(' + _ID + ')\\s+in\\s+(.+)\\s*$', 'u');

    // Sentinelas por componente: um x-for com expressão inválida não lê nada do
    // store, então não tem nenhuma dep real e nunca mais rodaria. Ele assina aqui e
    // _scheduleApply(key) o reagenda a cada atribuição no componente, reportando o
    // erro de novo (onError) sem travar os irmãos.
    const _forErrDeps = Object.create(null);

    function _forErrDep(key) {
        if (!key) return;
        if (!_forErrDeps[key]) _forErrDeps[key] = {};
        _track(_forErrDeps[key], 'v');
    }

    function _renderFor(node, parentScope, expr) {
        let alias, indexAlias, listExp;

        const matchAs = expr.match(_FOR_AS);
        const matchComma = expr.match(_FOR_COMMA);
        const matchPlain = expr.match(_FOR_PLAIN);

        if (matchAs) {
            alias = matchAs[1]; listExp = matchAs[2].trim(); indexAlias = matchAs[3];
        } else if (matchComma) {
            alias = matchComma[1]; indexAlias = matchComma[2]; listExp = matchComma[3].trim();
        } else if (matchPlain) {
            alias = matchPlain[1]; listExp = matchPlain[2].trim(); indexAlias = null;
        } else {
            const pe = _sGet(node, 'effect');
            _forErrDep(pe && pe.key);
            _reportError(ERROR_TYPES.X_FOR_SYNTAX, 'Expressão inválida no x-for', {
                expr: expr,
                element: _elementId(node),
                path: (pe && pe.key) || 'unknown',
            });
            return;
        }

        const list = _evalExpr(listExp, parentScope);
        const xKeyExpr = node.getAttribute('x-key') || null;

        if (_sGet(node, 'template') == null) _cacheNode(node);
        const template = _sGet(node, 'template');
        const statics = _sGet(node, 'statics') || { lead: [], trail: [] };
        const templateHasModel = !!template && template.indexOf('x-model') !== -1;

        // ── Lista vazia: destrói nós (effects + listeners), preserva x-static ──
        if (!Array.isArray(list) || list.length === 0) {
            (_sGet(node, 'groups') || []).forEach(function (g) {
                g.nodes.forEach(_destroyNode);
            });
            Array.from(node.children).forEach(function (c) {
                if (!_sGet(c, 'static')) c.remove();
            });
            _sSet(node, 'keys', []);
            _sSet(node, 'groups', []);
            return;
        }

        const parentEffect = _sGet(node, 'effect');
        const rootKey = parentEffect ? parentEffect.key : null;

        const rootEl = rootKey
            ? document.querySelector(
                '[x-data="' + CSS.escape(rootKey) + '"], [proxy-target="' + CSS.escape(rootKey) + '"]'
            )
            : null;

        const existingByKey = Object.create(null);
        const prevGroups = _sGet(node, 'groups') || [];
        const currentKeys = prevGroups.map(function (g) { return g.key; });
        prevGroups.forEach(function (g) { existingByKey[g.key] = g.nodes; });

        const newKeys = [];
        const newNodes = [];
        const newScopes = [];
        const newThis = [];
        const newNodeGroups = [];
        const newChanged = [];
        const seenKeys = new Set();

        list.forEach(function (item, index) {
            // Só Array/objeto literal vira proxy; primitivos, Date, Map, Set... usados direto
            const isObj = item !== null && typeof item === 'object';
            let itemWithIndex = item;
            if (isObj && (item[_PROXY_SYM] || _isProxyable(item))) {
                const rawItem = item[_PROXY_SYM] ? item : _makeProxy(item, rootKey || '');
                itemWithIndex = new Proxy(rawItem, {
                    get(target, prop, receiver) {
                        if (prop === '$i' || prop === '$index') return index;
                        return Reflect.get(target, prop, receiver);
                    }
                });
            }

            const parentThis = parentScope.$this || null;
            const itemThis = { index: index, dom: null, data: item, parent: parentThis };

            // Scope por prototype: herda o store e o scope do loop pai
            const own = {};
            own[alias] = itemWithIndex;
            own.$i = index;
            own.$index = index;
            own.$this = itemThis;
            if (indexAlias) own[indexAlias] = index;

            const scope = Object.create(parentScope);
            Object.keys(own).forEach(function (k) {
                Object.defineProperty(scope, k, { value: own[k], writable: true, enumerable: true, configurable: true });
            });
            Object.defineProperty(scope, _SCOPE_VARS, {
                value: (parentScope[_SCOPE_VARS] || []).concat(Object.keys(own)),
                writable: true, enumerable: false, configurable: true
            });

            const rawRef = isObj ? (item[_PROXY_SYM] ? item.__raw : item) : item;
            const baseKey = _getItemKey(item, xKeyExpr, scope);
            let key = baseKey;
            let dupCount = 1;
            while (seenKeys.has(key)) key = baseKey + '__' + (++dupCount);
            seenKeys.add(key);

            newKeys.push(key);
            newScopes.push(scope);
            newThis.push(itemThis);

            if (existingByKey[key]) {
                const groupNodes = existingByKey[key];
                let changed = false;
                groupNodes.forEach(function (existingEl) {
                    const eff = _sGet(existingEl, 'effect');
                    if (eff && !eff.dead && _sGet(existingEl, 'forIndex') === index && _sGet(existingEl, 'forItem') === rawRef) {
                        // Inalterado: o effect do nó já rastreia suas deps — só atualiza o scope
                        eff.scope = scope;
                        if (rootKey) eff.key = rootKey;
                    } else {
                        _renderTracked(existingEl, scope, rootKey);
                        _sSet(existingEl, 'forIndex', index);
                        _sSet(existingEl, 'forItem', rawRef);
                        changed = true;
                    }
                });
                newNodes.push.apply(newNodes, groupNodes);
                newNodeGroups.push(groupNodes);
                newChanged.push(changed);
            } else {
                const wrapper = _createWrapper(node);
                wrapper.innerHTML = template;
                _cacheTemplates(wrapper);
                const children = Array.from(wrapper.children);

                children.forEach(function (c) {
                    _renderTracked(c, scope, rootKey);
                    _sSet(c, 'forIndex', index);
                    _sSet(c, 'forItem', rawRef);
                });
                newNodes.push.apply(newNodes, children);
                newNodeGroups.push(children);
                newChanged.push(true);
            }
        });

        // ── Remove obsoletos ──────────────────────────────────────────────────
        const newKeySet = new Set(newKeys);
        currentKeys.forEach(function (key) {
            if (!newKeySet.has(key) && existingByKey[key]) {
                existingByKey[key].forEach(function (el) {
                    _destroyNode(el);
                    el.remove();
                });
            }
        });

        // ── Remove filhos extras não rastreados (preserva x-static) ───────────
        const newNodeSet = new Set(newNodes);
        Array.from(node.children).forEach(function (child) {
            if (!newNodeSet.has(child) && !_sGet(child, 'static')) child.remove();
        });

        // ── Insere/reordena (statics iniciais + itens + statics finais) ───────
        const expected = statics.lead.concat(newNodes, statics.trail);
        const needsReorder = expected.length !== node.children.length ||
            expected.some(function (el, i) { return node.children[i] !== el; });

        if (needsReorder) {
            const frag = document.createDocumentFragment();
            expected.forEach(function (el) { frag.appendChild(el); });
            node.appendChild(frag);
        }

        _sSet(node, 'keys', newKeys);
        _sSet(node, 'groups', newKeys.map(function (key, i) {
            return { key: key, nodes: newNodeGroups[i] };
        }));

        // ── $this.dom e bind de eventos / models (só itens novos ou movidos) ──
        const $ref = {};
        if (rootEl) {
            rootEl.querySelectorAll('[x-ref]').forEach(function (refEl) {
                $ref[refEl.getAttribute('x-ref')] = refEl;
            });
        }

        const $emit = function (name, detail) {
            if (!rootEl) return;
            rootEl.dispatchEvent(new CustomEvent(name, { bubbles: true, detail: detail || {} }));
        };

        newNodeGroups.forEach(function (nodes, i) {
            if (!newChanged[i]) return;
            newThis[i].dom = nodes[0] || null;

            const enrichedScope = Object.create(newScopes[i]);
            Object.defineProperties(enrichedScope, {
                $root: { value: rootEl, writable: true, enumerable: true, configurable: true },
                $ref: { value: $ref, writable: true, enumerable: true, configurable: true },
                $emit: { value: $emit, writable: true, enumerable: true, configurable: true }
            });

            nodes.forEach(function (el) {
                if (el && el.nodeType === Node.ELEMENT_NODE) {
                    _bindEvents(el, enrichedScope, rootKey);
                    if (templateHasModel) _bindModelsInLoop(el, enrichedScope, rootKey);
                }
            });
        });
    }


    // ─── Template cache ───────────────────────────────────────────────────────
    // Filhos com x-static ficam fora do template e são preservados pelo x-for.

    function _cacheNode(el) {
        if (_sGet(el, 'template') != null) return;

        const lead = [], trail = [];
        let seenItem = false;
        Array.from(el.children).forEach(function (c) {
            if (c.hasAttribute('x-static')) {
                _sSet(c, 'static', true);
                (seenItem ? trail : lead).push(c);
            } else {
                seenItem = true;
            }
        });

        let tpl;
        if (lead.length || trail.length) {
            const clone = el.cloneNode(true);
            Array.from(clone.children).forEach(function (c) {
                if (c.hasAttribute('x-static')) c.remove();
            });
            tpl = clone.innerHTML;
        } else {
            tpl = el.innerHTML;
        }

        _sSet(el, 'statics', { lead: lead, trail: trail });
        _sSet(el, 'template', tpl);
    }

    function _cacheTemplates(root) {
        root.querySelectorAll('[x-for]').forEach(_cacheNode);
    }

    // ─── Apply ────────────────────────────────────────────────────────────────

    function _applyTarget(key, doRender) {
        if (doRender === undefined) doRender = true;
        const targets = document.querySelectorAll(
            '[proxy-target="' + CSS.escape(key) + '"], [x-data="' + CSS.escape(key) + '"]'
        );

        if (!targets.length) return;

        const data = _store[key];
        if (!data) return;

        targets.forEach(function (target) {
            if (typeof data.$beforeRender === 'function') {
                try { data.$beforeRender(target); } catch (e) { _reportError(ERROR_TYPES.LIFECYCLE, '$beforeRender threw', { message: e.message, component: key }); }
            }
            target.dispatchEvent(new CustomEvent('before-render', { bubbles: false }));

            if (target.hasAttribute('x-for')) _cacheNode(target);
            _cacheTemplates(target);

            const $ref = {};
            target.querySelectorAll('[x-ref]').forEach(function (el) {
                $ref[el.getAttribute('x-ref')] = el;
            });
            const $emit = function (name, detail) {
                target.dispatchEvent(new CustomEvent(name, { bubbles: true, detail: detail || {} }));
            };

            const liveData = _proxies[key] || data;
            const baseScope = target.hasAttribute('x-data')
                ? liveData
                : { [key]: liveData };

            // Props OWN via defineProperties — nunca passam pelo set trap do proxy (evita loop de render).
            const scope = Object.create(baseScope);
            Object.defineProperties(scope, {
                $root: { value: target, writable: true, enumerable: true, configurable: true },
                $ref: { value: $ref, writable: true, enumerable: true, configurable: true },
                $emit: { value: $emit, writable: true, enumerable: true, configurable: true },
                $i: { value: undefined, writable: true, enumerable: true, configurable: true },
                $index: { value: undefined, writable: true, enumerable: true, configurable: true },
                $this: { value: null, writable: true, enumerable: true, configurable: true }
            });

            if (doRender) {
                _renderTracked(target, scope, key);
            }

            Promise.resolve().then(function () {
                _bindEvents(target, scope, key);

                if (_pendingBinds.has(key)) {
                    const pending = _pendingBinds.get(key);
                    _pendingBinds.delete(key);
                    pending.forEach(function (p) {
                        _bindEvents(p.el, p.scope, p.key);
                    });
                }

                // x-cloak: some após o 1º render
                if (target.hasAttribute('x-cloak')) target.removeAttribute('x-cloak');
                target.querySelectorAll('[x-cloak]').forEach(function (el) { el.removeAttribute('x-cloak'); });

                if (typeof data.$afterRender === 'function') {
                    try { data.$afterRender(target); } catch (e) { _reportError(ERROR_TYPES.LIFECYCLE, '$afterRender threw', { message: e.message, component: key }); }
                }
                target.dispatchEvent(new CustomEvent('after-render', { bubbles: false }));
            });
        });

        _syncModelsForKey(key);
    }

    // ─── Proxy factory ────────────────────────────────────────────────────────

    const _nestedProxyCache = new WeakMap();

    function _getNestedProxy(raw, key, path) {
        let byPath = _nestedProxyCache.get(raw);
        if (!byPath) { byPath = new Map(); _nestedProxyCache.set(raw, byPath); }
        const cacheKey = key + '\u0000' + path;
        if (byPath.has(cacheKey)) return byPath.get(cacheKey);
        const nested = _makeProxy(raw, key, path);
        byPath.set(cacheKey, nested);
        return nested;
    }

    function _makeProxy(data, key, _path) {
        const basePath = _path || key;
        return new Proxy(data, {
            get(target, prop, receiver) {
                if (prop === _PROXY_SYM) return true;
                if (prop === '__raw') return target;

                if (typeof prop === 'string') _track(target, prop);

                const val = Reflect.get(target, prop, receiver);
                if (val !== null && typeof val === 'object' && !val[_PROXY_SYM] && _isProxyable(val)) {
                    // Invariante do Proxy: prop não-configurável e não-gravável (frozen) deve devolver o valor real
                    if (!Object.isExtensible(target)) {
                        const d = Object.getOwnPropertyDescriptor(target, prop);
                        if (d && !d.configurable && !d.writable) return val;
                    }
                    return _getNestedProxy(val, key, basePath + '.' + String(prop));
                }
                return val;
            },

            set(target, prop, value) {
                // Unwrap: nunca grava proxy dentro do raw (sort/reverse/splice leem via proxy e regravam)
                if (value && typeof value === 'object' && value[_PROXY_SYM]) value = value.__raw;

                // Hooks de lifecycle não disparam render
                if (typeof prop === 'string' && _HOOKS.has(prop)) { target[prop] = value; return true; }

                const oldVal = target[prop];
                if (oldVal === value) return true;

                const path = basePath + '.' + String(prop);
                const ancestorSnapshots = _snapshotAncestors(path);
                const isArr = Array.isArray(target);
                const oldLen = isArr ? target.length : 0;

                target[prop] = value;

                _notifyWatchers(path, value, oldVal, ancestorSnapshots);

                // _scheduleApply ANTES do _trigger: $beforeRender roda antes dos effects granulares
                const handled = _hasEffects(target, prop);
                _scheduleApply(key, !handled);
                _trigger(target, prop);
                // push/índice novo: length muda sozinho e o set de 'length' sai cedo (oldVal === value)
                if (isArr && prop !== 'length' && target.length !== oldLen) _trigger(target, 'length');

                return true;
            },

            deleteProperty(target, prop) {
                if (!Object.prototype.hasOwnProperty.call(target, prop)) return true;

                const path = basePath + '.' + String(prop);
                const oldVal = target[prop];
                const ancestorSnapshots = _snapshotAncestors(path);

                delete target[prop];

                _notifyWatchers(path, undefined, oldVal, ancestorSnapshots);
                const handled = _hasEffects(target, prop);
                _scheduleApply(key, !handled);
                _trigger(target, prop);
                return true;
            }
        });
    }

    // ─── Destroy helpers ──────────────────────────────────────────────────────

    function _destroyNode(node) {
        if (!node || node.nodeType !== Node.ELEMENT_NODE) return;

        if (node.attributes) {
            for (let attr of Array.from(node.attributes)) {
                if (!attr.name.startsWith('x-on:')) continue;
                const event = attr.name.slice(5);
                const key = 'on_' + event;
                const handler = _sGet(node, key);
                if (handler) {
                    node.removeEventListener(event, handler);
                    _sDelete(node, key);
                }
                _sDelete(node, 'evScope_' + event);
            }
        }

        const nodeEffect = _sGet(node, 'effect');
        if (nodeEffect) {
            nodeEffect.kill();
            _sDelete(node, 'effect');
        }

        if (_sGet(node, 'model')) {
            const modelHandler = _sGet(node, 'modelHandler');
            if (modelHandler) {
                node.removeEventListener('input', modelHandler);
                node.removeEventListener('change', modelHandler);
                _sDelete(node, 'modelHandler');
            }
            const modelEffect = _sGet(node, 'modelEffect');
            if (modelEffect) {
                modelEffect.kill();
                _sDelete(node, 'modelEffect');
            }
            _sDelete(node, 'model');
            _sDelete(node, 'modelParts');
        }

        if (_sGet(node, 'loopModel')) {
            const loopModelHandler = _sGet(node, 'loopModelHandler');
            if (loopModelHandler) {
                node.removeEventListener('input', loopModelHandler);
                node.removeEventListener('change', loopModelHandler);
                _sDelete(node, 'loopModelHandler');
            }
            const loopModelEffect = _sGet(node, 'loopModelEffect');
            if (loopModelEffect) {
                loopModelEffect.kill();
                _sDelete(node, 'loopModelEffect');
            }
            _sDelete(node, 'loopModel');
            _sDelete(node, 'loopAlias');
        }

        Array.from(node.children).forEach(_destroyNode);
    }

    function _destroyKey(key) {
        _pendingKeys.delete(key);
        _pendingKeysNeedRender.delete(key);

        const targets = document.querySelectorAll(
            '[proxy-target="' + CSS.escape(key) + '"], [x-data="' + CSS.escape(key) + '"]'
        );

        targets.forEach(function (target) {
            const data = _store[key] || {};

            if (typeof data.$beforeDestroy === 'function') {
                try { data.$beforeDestroy(target); } catch (e) {
                    _reportError(ERROR_TYPES.LIFECYCLE, '$beforeDestroy threw', { message: e.message, component: key });
                }
            }
            target.dispatchEvent(new CustomEvent('before-destroy', { bubbles: false }));

            Array.from(target.children).forEach(_destroyNode);

            const targetEffect = _sGet(target, 'effect');
            if (targetEffect) {
                targetEffect.kill();
                _sDelete(target, 'effect');
            }
            _sDelete(target, 'keys');

            if (typeof data.$afterDestroy === 'function') {
                try { data.$afterDestroy(target); } catch (e) {
                    _reportError(ERROR_TYPES.LIFECYCLE, '$afterDestroy threw', { message: e.message, component: key });
                }
            }
            target.dispatchEvent(new CustomEvent('after-destroy', { bubbles: false }));
        });

        delete _store[key];
        delete _proxies[key];

        Object.keys(_watchers).forEach(function (path) {
            if (path === key || path.startsWith(key + '.')) delete _watchers[path];
        });

        _modelRegistryRemove(key);
        _pendingBinds.delete(key);
    }

    // ─── Public API ───────────────────────────────────────────────────────────
    return {

        name: 'shadow-proxy',
        version: '2.8.0',

        /** Proxy raiz dos stores: shadowProxy.template.<key>.<prop> = valor */
        template: {},

        /** Handler global de erros (substitui console.error). Recebe { type, message, timestamp, ... } */
        onError: null,

        /**
         * Observa qualquer caminho profundo do store. Retorna função de unsubscribe.
         * shadowProxy.on('carrinho.itens', (novo, antigo) => {})
         */
        on: function (path, fn) {
            return _registerWatcher(path, fn);
        },

        /** Registra x-on:* dentro de root (uso manual após injetar HTML dinâmico). */
        bindEvents: _bindEvents,

        /** Inicializa x-model no documento (ou em root). Chamar de novo após injetar HTML. */
        initModels: _initModels,

        /** Destrói um componente (key) ou todos. Dispara $beforeDestroy/$afterDestroy. */
        destroy: function (key) {
            if (key) {
                _destroyKey(key);
            } else {
                Object.keys(_store).forEach(_destroyKey);
            }
        },

        /** Inicializa o sistema reativo (após DOM pronto). Pode ser chamado de novo após destroy(). */
        initProxy: function () {
            const self = this;

            if (!document.getElementById('shadow-proxy-cloak')) {
                const st = document.createElement('style');
                st.id = 'shadow-proxy-cloak';
                st.textContent = '[x-cloak]{display:none!important}';
                (document.head || document.documentElement).appendChild(st);
            }

            document.querySelectorAll('[proxy-target], [x-data]').forEach(function (el) {
                const key = el.getAttribute('proxy-target') || el.getAttribute('x-data');
                if (!key) {
                    _reportError(ERROR_TYPES.PROXY_TARGET, 'x-data / proxy-target sem nome', { element: _elementId(el) });
                    return;
                }
                if (!_store[key]) _store[key] = {};
                if (!_proxies[key]) _proxies[key] = _makeProxy(_store[key], key);
                if (el.hasAttribute('x-for')) _cacheNode(el);
                _cacheTemplates(el);
                _scheduleApply(key);   // 1º render (limpa x-for vazio, remove x-cloak)
            });

            self.template = new Proxy(_store, {
                get(target, key) {
                    if (key === '__raw__') return target;
                    if (typeof key !== 'string' || key === 'then' || key === 'toJSON') return undefined;
                    if (!target[key]) target[key] = {};
                    if (!_proxies[key] || _proxies[key].__raw !== target[key]) {
                        _proxies[key] = _makeProxy(target[key], key);
                    }
                    const raw = target[key];
                    if (raw && typeof raw === 'object' && !_destroyBound.has(raw) && Object.isExtensible(raw)) {
                        Object.defineProperty(raw, 'destroy', {
                            configurable: true,
                            enumerable: false,
                            value: function () { _destroyKey(key); }
                        });
                        _destroyBound.add(raw);
                    }
                    return _proxies[key];
                },
                set(target, key, value) {
                    if (typeof key !== 'string') return false;
                    if (value && typeof value === 'object' && value[_PROXY_SYM]) value = value.__raw;

                    const oldVal = target[key];
                    target[key] = value;
                    if (value && typeof value === 'object') _proxies[key] = _makeProxy(value, key);
                    else delete _proxies[key];

                    // Watchers: caminho exato + descendentes
                    _notifyWatchers(key, value, oldVal, new Map());
                    Object.keys(_watchers).forEach(function (p) {
                        if (!p.startsWith(key + '.')) return;
                        const rest = p.slice(key.length + 1).split('.');
                        _notifyWatchers(p, _pick(value, rest), _pick(oldVal, rest), new Map(), true);
                    });

                    _scheduleApply(key);
                    return true;
                }
            });

            _initModels();
        }
    };

})();