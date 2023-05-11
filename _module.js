function noop() { }
const identity = x => x;
function assign(tar, src) {
    // @ts-ignore
    for (const k in src)
        tar[k] = src[k];
    return tar;
}
function run(fn) {
    return fn();
}
function blank_object() {
    return Object.create(null);
}
function run_all(fns) {
    fns.forEach(run);
}
function is_function(thing) {
    return typeof thing === 'function';
}
function safe_not_equal(a, b) {
    return a != a ? b == b : a !== b || ((a && typeof a === 'object') || typeof a === 'function');
}
let src_url_equal_anchor;
function src_url_equal(element_src, url) {
    if (!src_url_equal_anchor) {
        src_url_equal_anchor = document.createElement('a');
    }
    src_url_equal_anchor.href = url;
    return element_src === src_url_equal_anchor.href;
}
function is_empty(obj) {
    return Object.keys(obj).length === 0;
}
function exclude_internal_props(props) {
    const result = {};
    for (const k in props)
        if (k[0] !== '$')
            result[k] = props[k];
    return result;
}

const is_client = typeof window !== 'undefined';
let now = is_client
    ? () => window.performance.now()
    : () => Date.now();
let raf = is_client ? cb => requestAnimationFrame(cb) : noop;

const tasks = new Set();
function run_tasks(now) {
    tasks.forEach(task => {
        if (!task.c(now)) {
            tasks.delete(task);
            task.f();
        }
    });
    if (tasks.size !== 0)
        raf(run_tasks);
}
/**
 * Creates a new task that runs on each raf frame
 * until it returns a falsy value or is aborted
 */
function loop(callback) {
    let task;
    if (tasks.size === 0)
        raf(run_tasks);
    return {
        promise: new Promise(fulfill => {
            tasks.add(task = { c: callback, f: fulfill });
        }),
        abort() {
            tasks.delete(task);
        }
    };
}

// Track which nodes are claimed during hydration. Unclaimed nodes can then be removed from the DOM
// at the end of hydration without touching the remaining nodes.
let is_hydrating = false;
function start_hydrating() {
    is_hydrating = true;
}
function end_hydrating() {
    is_hydrating = false;
}
function upper_bound(low, high, key, value) {
    // Return first index of value larger than input value in the range [low, high)
    while (low < high) {
        const mid = low + ((high - low) >> 1);
        if (key(mid) <= value) {
            low = mid + 1;
        }
        else {
            high = mid;
        }
    }
    return low;
}
function init_hydrate(target) {
    if (target.hydrate_init)
        return;
    target.hydrate_init = true;
    // We know that all children have claim_order values since the unclaimed have been detached if target is not <head>
    let children = target.childNodes;
    // If target is <head>, there may be children without claim_order
    if (target.nodeName === 'HEAD') {
        const myChildren = [];
        for (let i = 0; i < children.length; i++) {
            const node = children[i];
            if (node.claim_order !== undefined) {
                myChildren.push(node);
            }
        }
        children = myChildren;
    }
    /*
    * Reorder claimed children optimally.
    * We can reorder claimed children optimally by finding the longest subsequence of
    * nodes that are already claimed in order and only moving the rest. The longest
    * subsequence of nodes that are claimed in order can be found by
    * computing the longest increasing subsequence of .claim_order values.
    *
    * This algorithm is optimal in generating the least amount of reorder operations
    * possible.
    *
    * Proof:
    * We know that, given a set of reordering operations, the nodes that do not move
    * always form an increasing subsequence, since they do not move among each other
    * meaning that they must be already ordered among each other. Thus, the maximal
    * set of nodes that do not move form a longest increasing subsequence.
    */
    // Compute longest increasing subsequence
    // m: subsequence length j => index k of smallest value that ends an increasing subsequence of length j
    const m = new Int32Array(children.length + 1);
    // Predecessor indices + 1
    const p = new Int32Array(children.length);
    m[0] = -1;
    let longest = 0;
    for (let i = 0; i < children.length; i++) {
        const current = children[i].claim_order;
        // Find the largest subsequence length such that it ends in a value less than our current value
        // upper_bound returns first greater value, so we subtract one
        // with fast path for when we are on the current longest subsequence
        const seqLen = ((longest > 0 && children[m[longest]].claim_order <= current) ? longest + 1 : upper_bound(1, longest, idx => children[m[idx]].claim_order, current)) - 1;
        p[i] = m[seqLen] + 1;
        const newLen = seqLen + 1;
        // We can guarantee that current is the smallest value. Otherwise, we would have generated a longer sequence.
        m[newLen] = i;
        longest = Math.max(newLen, longest);
    }
    // The longest increasing subsequence of nodes (initially reversed)
    const lis = [];
    // The rest of the nodes, nodes that will be moved
    const toMove = [];
    let last = children.length - 1;
    for (let cur = m[longest] + 1; cur != 0; cur = p[cur - 1]) {
        lis.push(children[cur - 1]);
        for (; last >= cur; last--) {
            toMove.push(children[last]);
        }
        last--;
    }
    for (; last >= 0; last--) {
        toMove.push(children[last]);
    }
    lis.reverse();
    // We sort the nodes being moved to guarantee that their insertion order matches the claim order
    toMove.sort((a, b) => a.claim_order - b.claim_order);
    // Finally, we move the nodes
    for (let i = 0, j = 0; i < toMove.length; i++) {
        while (j < lis.length && toMove[i].claim_order >= lis[j].claim_order) {
            j++;
        }
        const anchor = j < lis.length ? lis[j] : null;
        target.insertBefore(toMove[i], anchor);
    }
}
function append(target, node) {
    target.appendChild(node);
}
function get_root_for_style(node) {
    if (!node)
        return document;
    const root = node.getRootNode ? node.getRootNode() : node.ownerDocument;
    if (root && root.host) {
        return root;
    }
    return node.ownerDocument;
}
function append_empty_stylesheet(node) {
    const style_element = element('style');
    append_stylesheet(get_root_for_style(node), style_element);
    return style_element.sheet;
}
function append_stylesheet(node, style) {
    append(node.head || node, style);
    return style.sheet;
}
function append_hydration(target, node) {
    if (is_hydrating) {
        init_hydrate(target);
        if ((target.actual_end_child === undefined) || ((target.actual_end_child !== null) && (target.actual_end_child.parentNode !== target))) {
            target.actual_end_child = target.firstChild;
        }
        // Skip nodes of undefined ordering
        while ((target.actual_end_child !== null) && (target.actual_end_child.claim_order === undefined)) {
            target.actual_end_child = target.actual_end_child.nextSibling;
        }
        if (node !== target.actual_end_child) {
            // We only insert if the ordering of this node should be modified or the parent node is not target
            if (node.claim_order !== undefined || node.parentNode !== target) {
                target.insertBefore(node, target.actual_end_child);
            }
        }
        else {
            target.actual_end_child = node.nextSibling;
        }
    }
    else if (node.parentNode !== target || node.nextSibling !== null) {
        target.appendChild(node);
    }
}
function insert_hydration(target, node, anchor) {
    if (is_hydrating && !anchor) {
        append_hydration(target, node);
    }
    else if (node.parentNode !== target || node.nextSibling != anchor) {
        target.insertBefore(node, anchor || null);
    }
}
function detach(node) {
    if (node.parentNode) {
        node.parentNode.removeChild(node);
    }
}
function destroy_each(iterations, detaching) {
    for (let i = 0; i < iterations.length; i += 1) {
        if (iterations[i])
            iterations[i].d(detaching);
    }
}
function element(name) {
    return document.createElement(name);
}
function svg_element(name) {
    return document.createElementNS('http://www.w3.org/2000/svg', name);
}
function text(data) {
    return document.createTextNode(data);
}
function space() {
    return text(' ');
}
function empty() {
    return text('');
}
function listen(node, event, handler, options) {
    node.addEventListener(event, handler, options);
    return () => node.removeEventListener(event, handler, options);
}
function attr(node, attribute, value) {
    if (value == null)
        node.removeAttribute(attribute);
    else if (node.getAttribute(attribute) !== value)
        node.setAttribute(attribute, value);
}
/**
 * List of attributes that should always be set through the attr method,
 * because updating them through the property setter doesn't work reliably.
 * In the example of `width`/`height`, the problem is that the setter only
 * accepts numeric values, but the attribute can also be set to a string like `50%`.
 * If this list becomes too big, rethink this approach.
 */
const always_set_through_set_attribute = ['width', 'height'];
function set_attributes(node, attributes) {
    // @ts-ignore
    const descriptors = Object.getOwnPropertyDescriptors(node.__proto__);
    for (const key in attributes) {
        if (attributes[key] == null) {
            node.removeAttribute(key);
        }
        else if (key === 'style') {
            node.style.cssText = attributes[key];
        }
        else if (key === '__value') {
            node.value = node[key] = attributes[key];
        }
        else if (descriptors[key] && descriptors[key].set && always_set_through_set_attribute.indexOf(key) === -1) {
            node[key] = attributes[key];
        }
        else {
            attr(node, key, attributes[key]);
        }
    }
}
function set_svg_attributes(node, attributes) {
    for (const key in attributes) {
        attr(node, key, attributes[key]);
    }
}
function children(element) {
    return Array.from(element.childNodes);
}
function init_claim_info(nodes) {
    if (nodes.claim_info === undefined) {
        nodes.claim_info = { last_index: 0, total_claimed: 0 };
    }
}
function claim_node(nodes, predicate, processNode, createNode, dontUpdateLastIndex = false) {
    // Try to find nodes in an order such that we lengthen the longest increasing subsequence
    init_claim_info(nodes);
    const resultNode = (() => {
        // We first try to find an element after the previous one
        for (let i = nodes.claim_info.last_index; i < nodes.length; i++) {
            const node = nodes[i];
            if (predicate(node)) {
                const replacement = processNode(node);
                if (replacement === undefined) {
                    nodes.splice(i, 1);
                }
                else {
                    nodes[i] = replacement;
                }
                if (!dontUpdateLastIndex) {
                    nodes.claim_info.last_index = i;
                }
                return node;
            }
        }
        // Otherwise, we try to find one before
        // We iterate in reverse so that we don't go too far back
        for (let i = nodes.claim_info.last_index - 1; i >= 0; i--) {
            const node = nodes[i];
            if (predicate(node)) {
                const replacement = processNode(node);
                if (replacement === undefined) {
                    nodes.splice(i, 1);
                }
                else {
                    nodes[i] = replacement;
                }
                if (!dontUpdateLastIndex) {
                    nodes.claim_info.last_index = i;
                }
                else if (replacement === undefined) {
                    // Since we spliced before the last_index, we decrease it
                    nodes.claim_info.last_index--;
                }
                return node;
            }
        }
        // If we can't find any matching node, we create a new one
        return createNode();
    })();
    resultNode.claim_order = nodes.claim_info.total_claimed;
    nodes.claim_info.total_claimed += 1;
    return resultNode;
}
function claim_element_base(nodes, name, attributes, create_element) {
    return claim_node(nodes, (node) => node.nodeName === name, (node) => {
        const remove = [];
        for (let j = 0; j < node.attributes.length; j++) {
            const attribute = node.attributes[j];
            if (!attributes[attribute.name]) {
                remove.push(attribute.name);
            }
        }
        remove.forEach(v => node.removeAttribute(v));
        return undefined;
    }, () => create_element(name));
}
function claim_element(nodes, name, attributes) {
    return claim_element_base(nodes, name, attributes, element);
}
function claim_svg_element(nodes, name, attributes) {
    return claim_element_base(nodes, name, attributes, svg_element);
}
function claim_text(nodes, data) {
    return claim_node(nodes, (node) => node.nodeType === 3, (node) => {
        const dataStr = '' + data;
        if (node.data.startsWith(dataStr)) {
            if (node.data.length !== dataStr.length) {
                return node.splitText(dataStr.length);
            }
        }
        else {
            node.data = dataStr;
        }
    }, () => text(data), true // Text nodes should not update last index since it is likely not worth it to eliminate an increasing subsequence of actual elements
    );
}
function claim_space(nodes) {
    return claim_text(nodes, ' ');
}
function set_data(text, data) {
    data = '' + data;
    if (text.data === data)
        return;
    text.data = data;
}
function toggle_class(element, name, toggle) {
    element.classList[toggle ? 'add' : 'remove'](name);
}
function custom_event(type, detail, { bubbles = false, cancelable = false } = {}) {
    const e = document.createEvent('CustomEvent');
    e.initCustomEvent(type, bubbles, cancelable, detail);
    return e;
}
function head_selector(nodeId, head) {
    const result = [];
    let started = 0;
    for (const node of head.childNodes) {
        if (node.nodeType === 8 /* comment node */) {
            const comment = node.textContent.trim();
            if (comment === `HEAD_${nodeId}_END`) {
                started -= 1;
                result.push(node);
            }
            else if (comment === `HEAD_${nodeId}_START`) {
                started += 1;
                result.push(node);
            }
        }
        else if (started > 0) {
            result.push(node);
        }
    }
    return result;
}

// we need to store the information for multiple documents because a Svelte application could also contain iframes
// https://github.com/sveltejs/svelte/issues/3624
const managed_styles = new Map();
let active = 0;
// https://github.com/darkskyapp/string-hash/blob/master/index.js
function hash(str) {
    let hash = 5381;
    let i = str.length;
    while (i--)
        hash = ((hash << 5) - hash) ^ str.charCodeAt(i);
    return hash >>> 0;
}
function create_style_information(doc, node) {
    const info = { stylesheet: append_empty_stylesheet(node), rules: {} };
    managed_styles.set(doc, info);
    return info;
}
function create_rule(node, a, b, duration, delay, ease, fn, uid = 0) {
    const step = 16.666 / duration;
    let keyframes = '{\n';
    for (let p = 0; p <= 1; p += step) {
        const t = a + (b - a) * ease(p);
        keyframes += p * 100 + `%{${fn(t, 1 - t)}}\n`;
    }
    const rule = keyframes + `100% {${fn(b, 1 - b)}}\n}`;
    const name = `__svelte_${hash(rule)}_${uid}`;
    const doc = get_root_for_style(node);
    const { stylesheet, rules } = managed_styles.get(doc) || create_style_information(doc, node);
    if (!rules[name]) {
        rules[name] = true;
        stylesheet.insertRule(`@keyframes ${name} ${rule}`, stylesheet.cssRules.length);
    }
    const animation = node.style.animation || '';
    node.style.animation = `${animation ? `${animation}, ` : ''}${name} ${duration}ms linear ${delay}ms 1 both`;
    active += 1;
    return name;
}
function delete_rule(node, name) {
    const previous = (node.style.animation || '').split(', ');
    const next = previous.filter(name
        ? anim => anim.indexOf(name) < 0 // remove specific animation
        : anim => anim.indexOf('__svelte') === -1 // remove all Svelte animations
    );
    const deleted = previous.length - next.length;
    if (deleted) {
        node.style.animation = next.join(', ');
        active -= deleted;
        if (!active)
            clear_rules();
    }
}
function clear_rules() {
    raf(() => {
        if (active)
            return;
        managed_styles.forEach(info => {
            const { ownerNode } = info.stylesheet;
            // there is no ownerNode if it runs on jsdom.
            if (ownerNode)
                detach(ownerNode);
        });
        managed_styles.clear();
    });
}

let current_component;
function set_current_component(component) {
    current_component = component;
}
function get_current_component() {
    if (!current_component)
        throw new Error('Function called outside component initialization');
    return current_component;
}
/**
 * The `onMount` function schedules a callback to run as soon as the component has been mounted to the DOM.
 * It must be called during the component's initialisation (but doesn't need to live *inside* the component;
 * it can be called from an external module).
 *
 * `onMount` does not run inside a [server-side component](/docs#run-time-server-side-component-api).
 *
 * https://svelte.dev/docs#run-time-svelte-onmount
 */
function onMount(fn) {
    get_current_component().$$.on_mount.push(fn);
}
/**
 * Schedules a callback to run immediately before the component is unmounted.
 *
 * Out of `onMount`, `beforeUpdate`, `afterUpdate` and `onDestroy`, this is the
 * only one that runs inside a server-side component.
 *
 * https://svelte.dev/docs#run-time-svelte-ondestroy
 */
function onDestroy(fn) {
    get_current_component().$$.on_destroy.push(fn);
}
/**
 * Creates an event dispatcher that can be used to dispatch [component events](/docs#template-syntax-component-directives-on-eventname).
 * Event dispatchers are functions that can take two arguments: `name` and `detail`.
 *
 * Component events created with `createEventDispatcher` create a
 * [CustomEvent](https://developer.mozilla.org/en-US/docs/Web/API/CustomEvent).
 * These events do not [bubble](https://developer.mozilla.org/en-US/docs/Learn/JavaScript/Building_blocks/Events#Event_bubbling_and_capture).
 * The `detail` argument corresponds to the [CustomEvent.detail](https://developer.mozilla.org/en-US/docs/Web/API/CustomEvent/detail)
 * property and can contain any type of data.
 *
 * https://svelte.dev/docs#run-time-svelte-createeventdispatcher
 */
function createEventDispatcher() {
    const component = get_current_component();
    return (type, detail, { cancelable = false } = {}) => {
        const callbacks = component.$$.callbacks[type];
        if (callbacks) {
            // TODO are there situations where events could be dispatched
            // in a server (non-DOM) environment?
            const event = custom_event(type, detail, { cancelable });
            callbacks.slice().forEach(fn => {
                fn.call(component, event);
            });
            return !event.defaultPrevented;
        }
        return true;
    };
}

const dirty_components = [];
const binding_callbacks = [];
let render_callbacks = [];
const flush_callbacks = [];
const resolved_promise = /* @__PURE__ */ Promise.resolve();
let update_scheduled = false;
function schedule_update() {
    if (!update_scheduled) {
        update_scheduled = true;
        resolved_promise.then(flush);
    }
}
function add_render_callback(fn) {
    render_callbacks.push(fn);
}
// flush() calls callbacks in this order:
// 1. All beforeUpdate callbacks, in order: parents before children
// 2. All bind:this callbacks, in reverse order: children before parents.
// 3. All afterUpdate callbacks, in order: parents before children. EXCEPT
//    for afterUpdates called during the initial onMount, which are called in
//    reverse order: children before parents.
// Since callbacks might update component values, which could trigger another
// call to flush(), the following steps guard against this:
// 1. During beforeUpdate, any updated components will be added to the
//    dirty_components array and will cause a reentrant call to flush(). Because
//    the flush index is kept outside the function, the reentrant call will pick
//    up where the earlier call left off and go through all dirty components. The
//    current_component value is saved and restored so that the reentrant call will
//    not interfere with the "parent" flush() call.
// 2. bind:this callbacks cannot trigger new flush() calls.
// 3. During afterUpdate, any updated components will NOT have their afterUpdate
//    callback called a second time; the seen_callbacks set, outside the flush()
//    function, guarantees this behavior.
const seen_callbacks = new Set();
let flushidx = 0; // Do *not* move this inside the flush() function
function flush() {
    // Do not reenter flush while dirty components are updated, as this can
    // result in an infinite loop. Instead, let the inner flush handle it.
    // Reentrancy is ok afterwards for bindings etc.
    if (flushidx !== 0) {
        return;
    }
    const saved_component = current_component;
    do {
        // first, call beforeUpdate functions
        // and update components
        try {
            while (flushidx < dirty_components.length) {
                const component = dirty_components[flushidx];
                flushidx++;
                set_current_component(component);
                update(component.$$);
            }
        }
        catch (e) {
            // reset dirty state to not end up in a deadlocked state and then rethrow
            dirty_components.length = 0;
            flushidx = 0;
            throw e;
        }
        set_current_component(null);
        dirty_components.length = 0;
        flushidx = 0;
        while (binding_callbacks.length)
            binding_callbacks.pop()();
        // then, once components are updated, call
        // afterUpdate functions. This may cause
        // subsequent updates...
        for (let i = 0; i < render_callbacks.length; i += 1) {
            const callback = render_callbacks[i];
            if (!seen_callbacks.has(callback)) {
                // ...so guard against infinite loops
                seen_callbacks.add(callback);
                callback();
            }
        }
        render_callbacks.length = 0;
    } while (dirty_components.length);
    while (flush_callbacks.length) {
        flush_callbacks.pop()();
    }
    update_scheduled = false;
    seen_callbacks.clear();
    set_current_component(saved_component);
}
function update($$) {
    if ($$.fragment !== null) {
        $$.update();
        run_all($$.before_update);
        const dirty = $$.dirty;
        $$.dirty = [-1];
        $$.fragment && $$.fragment.p($$.ctx, dirty);
        $$.after_update.forEach(add_render_callback);
    }
}
/**
 * Useful for example to execute remaining `afterUpdate` callbacks before executing `destroy`.
 */
function flush_render_callbacks(fns) {
    const filtered = [];
    const targets = [];
    render_callbacks.forEach((c) => fns.indexOf(c) === -1 ? filtered.push(c) : targets.push(c));
    targets.forEach((c) => c());
    render_callbacks = filtered;
}

let promise;
function wait() {
    if (!promise) {
        promise = Promise.resolve();
        promise.then(() => {
            promise = null;
        });
    }
    return promise;
}
function dispatch(node, direction, kind) {
    node.dispatchEvent(custom_event(`${direction ? 'intro' : 'outro'}${kind}`));
}
const outroing = new Set();
let outros;
function group_outros() {
    outros = {
        r: 0,
        c: [],
        p: outros // parent group
    };
}
function check_outros() {
    if (!outros.r) {
        run_all(outros.c);
    }
    outros = outros.p;
}
function transition_in(block, local) {
    if (block && block.i) {
        outroing.delete(block);
        block.i(local);
    }
}
function transition_out(block, local, detach, callback) {
    if (block && block.o) {
        if (outroing.has(block))
            return;
        outroing.add(block);
        outros.c.push(() => {
            outroing.delete(block);
            if (callback) {
                if (detach)
                    block.d(1);
                callback();
            }
        });
        block.o(local);
    }
    else if (callback) {
        callback();
    }
}
const null_transition = { duration: 0 };
function create_in_transition(node, fn, params) {
    const options = { direction: 'in' };
    let config = fn(node, params, options);
    let running = false;
    let animation_name;
    let task;
    let uid = 0;
    function cleanup() {
        if (animation_name)
            delete_rule(node, animation_name);
    }
    function go() {
        const { delay = 0, duration = 300, easing = identity, tick = noop, css } = config || null_transition;
        if (css)
            animation_name = create_rule(node, 0, 1, duration, delay, easing, css, uid++);
        tick(0, 1);
        const start_time = now() + delay;
        const end_time = start_time + duration;
        if (task)
            task.abort();
        running = true;
        add_render_callback(() => dispatch(node, true, 'start'));
        task = loop(now => {
            if (running) {
                if (now >= end_time) {
                    tick(1, 0);
                    dispatch(node, true, 'end');
                    cleanup();
                    return running = false;
                }
                if (now >= start_time) {
                    const t = easing((now - start_time) / duration);
                    tick(t, 1 - t);
                }
            }
            return running;
        });
    }
    let started = false;
    return {
        start() {
            if (started)
                return;
            started = true;
            delete_rule(node);
            if (is_function(config)) {
                config = config(options);
                wait().then(go);
            }
            else {
                go();
            }
        },
        invalidate() {
            started = false;
        },
        end() {
            if (running) {
                cleanup();
                running = false;
            }
        }
    };
}
function create_bidirectional_transition(node, fn, params, intro) {
    const options = { direction: 'both' };
    let config = fn(node, params, options);
    let t = intro ? 0 : 1;
    let running_program = null;
    let pending_program = null;
    let animation_name = null;
    function clear_animation() {
        if (animation_name)
            delete_rule(node, animation_name);
    }
    function init(program, duration) {
        const d = (program.b - t);
        duration *= Math.abs(d);
        return {
            a: t,
            b: program.b,
            d,
            duration,
            start: program.start,
            end: program.start + duration,
            group: program.group
        };
    }
    function go(b) {
        const { delay = 0, duration = 300, easing = identity, tick = noop, css } = config || null_transition;
        const program = {
            start: now() + delay,
            b
        };
        if (!b) {
            // @ts-ignore todo: improve typings
            program.group = outros;
            outros.r += 1;
        }
        if (running_program || pending_program) {
            pending_program = program;
        }
        else {
            // if this is an intro, and there's a delay, we need to do
            // an initial tick and/or apply CSS animation immediately
            if (css) {
                clear_animation();
                animation_name = create_rule(node, t, b, duration, delay, easing, css);
            }
            if (b)
                tick(0, 1);
            running_program = init(program, duration);
            add_render_callback(() => dispatch(node, b, 'start'));
            loop(now => {
                if (pending_program && now > pending_program.start) {
                    running_program = init(pending_program, duration);
                    pending_program = null;
                    dispatch(node, running_program.b, 'start');
                    if (css) {
                        clear_animation();
                        animation_name = create_rule(node, t, running_program.b, running_program.duration, 0, easing, config.css);
                    }
                }
                if (running_program) {
                    if (now >= running_program.end) {
                        tick(t = running_program.b, 1 - t);
                        dispatch(node, running_program.b, 'end');
                        if (!pending_program) {
                            // we're done
                            if (running_program.b) {
                                // intro — we can tidy up immediately
                                clear_animation();
                            }
                            else {
                                // outro — needs to be coordinated
                                if (!--running_program.group.r)
                                    run_all(running_program.group.c);
                            }
                        }
                        running_program = null;
                    }
                    else if (now >= running_program.start) {
                        const p = now - running_program.start;
                        t = running_program.a + running_program.d * easing(p / running_program.duration);
                        tick(t, 1 - t);
                    }
                }
                return !!(running_program || pending_program);
            });
        }
    }
    return {
        run(b) {
            if (is_function(config)) {
                wait().then(() => {
                    // @ts-ignore
                    config = config(options);
                    go(b);
                });
            }
            else {
                go(b);
            }
        },
        end() {
            clear_animation();
            running_program = pending_program = null;
        }
    };
}

function destroy_block(block, lookup) {
    block.d(1);
    lookup.delete(block.key);
}
function update_keyed_each(old_blocks, dirty, get_key, dynamic, ctx, list, lookup, node, destroy, create_each_block, next, get_context) {
    let o = old_blocks.length;
    let n = list.length;
    let i = o;
    const old_indexes = {};
    while (i--)
        old_indexes[old_blocks[i].key] = i;
    const new_blocks = [];
    const new_lookup = new Map();
    const deltas = new Map();
    const updates = [];
    i = n;
    while (i--) {
        const child_ctx = get_context(ctx, list, i);
        const key = get_key(child_ctx);
        let block = lookup.get(key);
        if (!block) {
            block = create_each_block(key, child_ctx);
            block.c();
        }
        else if (dynamic) {
            // defer updates until all the DOM shuffling is done
            updates.push(() => block.p(child_ctx, dirty));
        }
        new_lookup.set(key, new_blocks[i] = block);
        if (key in old_indexes)
            deltas.set(key, Math.abs(i - old_indexes[key]));
    }
    const will_move = new Set();
    const did_move = new Set();
    function insert(block) {
        transition_in(block, 1);
        block.m(node, next);
        lookup.set(block.key, block);
        next = block.first;
        n--;
    }
    while (o && n) {
        const new_block = new_blocks[n - 1];
        const old_block = old_blocks[o - 1];
        const new_key = new_block.key;
        const old_key = old_block.key;
        if (new_block === old_block) {
            // do nothing
            next = new_block.first;
            o--;
            n--;
        }
        else if (!new_lookup.has(old_key)) {
            // remove old block
            destroy(old_block, lookup);
            o--;
        }
        else if (!lookup.has(new_key) || will_move.has(new_key)) {
            insert(new_block);
        }
        else if (did_move.has(old_key)) {
            o--;
        }
        else if (deltas.get(new_key) > deltas.get(old_key)) {
            did_move.add(new_key);
            insert(new_block);
        }
        else {
            will_move.add(old_key);
            o--;
        }
    }
    while (o--) {
        const old_block = old_blocks[o];
        if (!new_lookup.has(old_block.key))
            destroy(old_block, lookup);
    }
    while (n)
        insert(new_blocks[n - 1]);
    run_all(updates);
    return new_blocks;
}

function get_spread_update(levels, updates) {
    const update = {};
    const to_null_out = {};
    const accounted_for = { $$scope: 1 };
    let i = levels.length;
    while (i--) {
        const o = levels[i];
        const n = updates[i];
        if (n) {
            for (const key in o) {
                if (!(key in n))
                    to_null_out[key] = 1;
            }
            for (const key in n) {
                if (!accounted_for[key]) {
                    update[key] = n[key];
                    accounted_for[key] = 1;
                }
            }
            levels[i] = n;
        }
        else {
            for (const key in o) {
                accounted_for[key] = 1;
            }
        }
    }
    for (const key in to_null_out) {
        if (!(key in update))
            update[key] = undefined;
    }
    return update;
}
function create_component(block) {
    block && block.c();
}
function claim_component(block, parent_nodes) {
    block && block.l(parent_nodes);
}
function mount_component(component, target, anchor, customElement) {
    const { fragment, after_update } = component.$$;
    fragment && fragment.m(target, anchor);
    if (!customElement) {
        // onMount happens before the initial afterUpdate
        add_render_callback(() => {
            const new_on_destroy = component.$$.on_mount.map(run).filter(is_function);
            // if the component was destroyed immediately
            // it will update the `$$.on_destroy` reference to `null`.
            // the destructured on_destroy may still reference to the old array
            if (component.$$.on_destroy) {
                component.$$.on_destroy.push(...new_on_destroy);
            }
            else {
                // Edge case - component was destroyed immediately,
                // most likely as a result of a binding initialising
                run_all(new_on_destroy);
            }
            component.$$.on_mount = [];
        });
    }
    after_update.forEach(add_render_callback);
}
function destroy_component(component, detaching) {
    const $$ = component.$$;
    if ($$.fragment !== null) {
        flush_render_callbacks($$.after_update);
        run_all($$.on_destroy);
        $$.fragment && $$.fragment.d(detaching);
        // TODO null out other refs, including component.$$ (but need to
        // preserve final state?)
        $$.on_destroy = $$.fragment = null;
        $$.ctx = [];
    }
}
function make_dirty(component, i) {
    if (component.$$.dirty[0] === -1) {
        dirty_components.push(component);
        schedule_update();
        component.$$.dirty.fill(0);
    }
    component.$$.dirty[(i / 31) | 0] |= (1 << (i % 31));
}
function init(component, options, instance, create_fragment, not_equal, props, append_styles, dirty = [-1]) {
    const parent_component = current_component;
    set_current_component(component);
    const $$ = component.$$ = {
        fragment: null,
        ctx: [],
        // state
        props,
        update: noop,
        not_equal,
        bound: blank_object(),
        // lifecycle
        on_mount: [],
        on_destroy: [],
        on_disconnect: [],
        before_update: [],
        after_update: [],
        context: new Map(options.context || (parent_component ? parent_component.$$.context : [])),
        // everything else
        callbacks: blank_object(),
        dirty,
        skip_bound: false,
        root: options.target || parent_component.$$.root
    };
    append_styles && append_styles($$.root);
    let ready = false;
    $$.ctx = instance
        ? instance(component, options.props || {}, (i, ret, ...rest) => {
            const value = rest.length ? rest[0] : ret;
            if ($$.ctx && not_equal($$.ctx[i], $$.ctx[i] = value)) {
                if (!$$.skip_bound && $$.bound[i])
                    $$.bound[i](value);
                if (ready)
                    make_dirty(component, i);
            }
            return ret;
        })
        : [];
    $$.update();
    ready = true;
    run_all($$.before_update);
    // `false` as a special case of no DOM component
    $$.fragment = create_fragment ? create_fragment($$.ctx) : false;
    if (options.target) {
        if (options.hydrate) {
            start_hydrating();
            const nodes = children(options.target);
            // eslint-disable-next-line @typescript-eslint/no-non-null-assertion
            $$.fragment && $$.fragment.l(nodes);
            nodes.forEach(detach);
        }
        else {
            // eslint-disable-next-line @typescript-eslint/no-non-null-assertion
            $$.fragment && $$.fragment.c();
        }
        if (options.intro)
            transition_in(component.$$.fragment);
        mount_component(component, options.target, options.anchor, options.customElement);
        end_hydrating();
        flush();
    }
    set_current_component(parent_component);
}
/**
 * Base class for Svelte components. Used when dev=false.
 */
class SvelteComponent {
    $destroy() {
        destroy_component(this, 1);
        this.$destroy = noop;
    }
    $on(type, callback) {
        if (!is_function(callback)) {
            return noop;
        }
        const callbacks = (this.$$.callbacks[type] || (this.$$.callbacks[type] = []));
        callbacks.push(callback);
        return () => {
            const index = callbacks.indexOf(callback);
            if (index !== -1)
                callbacks.splice(index, 1);
        };
    }
    $set($$props) {
        if (this.$$set && !is_empty($$props)) {
            this.$$.skip_bound = true;
            this.$$set($$props);
            this.$$.skip_bound = false;
        }
    }
}

/* generated by Svelte v3.58.0 */

function create_fragment(ctx) {
	let meta0;
	let meta1;
	let link;
	let style;
	let t;

	return {
		c() {
			meta0 = element("meta");
			meta1 = element("meta");
			link = element("link");
			style = element("style");
			t = text("@import url(\"https://unpkg.com/@primo-app/primo@1.3.64/reset.css\");\n\nhtml {\n  /* Colors */\n  --color-accent: #95B4BE;  \n  --font-primary: \"Bespoke Serif\", serif;\n  --font-secondary: system-ui, serif;\n\n  /* Default property values */\n  --background: white;\n  --color: #222;\n  --padding: 4rem 2rem;\n  --box-shadow: 0px 4px 30px rgba(0, 0, 0, 0.2);\n  --border-radius: 8px;\n  --max-width: 900px;\n  --border-color: #C6CCD2; \n  --transition-time: 0.1s;\n  --transition: var(--transition-time) color,\n    var(--transition-time) background-color,\n      var(--transition-time) border-color,\n        var(--transition-time) text-decoration-color,\n          var(--transition-time) box-shadow, var(--transtion-time) transform;\n}\n\n#page {\n  color: var(--color);\n  line-height: 1.6;\n  font-size: 1rem;\n  background: var(--background);\n}\n\n.section .content {\n  padding: var(--padding);\n  max-width: var(--max-width);\n  margin: 0 auto;\n}\n\n.section .content > * {\n    max-width: 700px;\n  }\n\n.section .content img {\n    width: 100%;\n    margin: 2rem 0;\n    box-shadow: var(--box-shadow);\n    border-radius: var(--border-radius);\n  }\n\n.section .content p {\n    padding: 0.5rem 0;\n    line-height: 1.5;\n  }\n\n.section .content a {\n\n  }\n\n.section .content h1 {\n    font-family: var(--font-primary);\n    font-size: 3rem;\n    font-weight: 700;\n    margin-bottom: 1rem;\n  }\n\n.section .content h2 {\n    font-family: var(--font-primary);\n    font-size: 1.75rem;\n    margin-bottom: 0.5rem;\n    font-weight: 500;\n\n   /* &:after {\n      width: 50px;\n      border-bottom: 3px solid var(--color);\n      content: \"\";\n      display: block;\n      margin-bottom: 1.5rem;\n      margin-top: 0.5rem;\n    }*/\n  }\n\n.section .content h3 {\n    font-family: var(--font-primary);\n    font-size: 1.5rem;\n    font-weight: 600;\n    margin-bottom: 0.25rem;\n  }\n\n.section .content ul {\n    list-style: disc;\n    padding: 0.5rem 0;\n    padding-left: 1.25rem;\n  }\n\n.section .content ol {\n    list-style: decimal;\n    padding: 0.5rem 0;\n    padding-left: 1.25rem;\n  }\n\n.section .content blockquote {\n    padding: 2rem;\n    box-shadow: var(--box-shadow);\n    border-radius: var(--border-radius);\n  }\n\n.section-container {\n  max-width: var(--max-width, 1200px);\n  margin: 0 auto;\n  padding: var(--padding); \n}\n\n.heading {\n  font-family: var(--font-primary);\n  font-size: 1.75rem; \n  line-height: 1;\n  font-weight: 500;\n  \n/*\n  &:after {\n    width: 50px;\n    border-bottom: 3px solid var(--color);\n    content: \"\";\n    display: block;\n    padding-top: 1rem;\n    margin-bottom: 1.5rem;\n  }\n  */\n}\n\n.link {\n  border-bottom: 1.5px solid #4C4E52;\n  transition: 0.1s border-color;\n}\n\n.link:hover {\n    border-color: transparent; \n  }\n\n.button {\n  color: white;\n  background: var(--color-accent);\n  border-radius: 5px;\n  padding: 8px 20px;\n  transition: var(--transition);\n}\n\n.button:hover {\n    box-shadow: 0 0 10px 5px rgba(0, 0, 0, 0.1);\n  }\n\n.button.inverted {\n    background: transparent;\n    color: var(--color-accent);\n    border: 2px solid var(--color-accent);\n  }");
			this.h();
		},
		l(nodes) {
			const head_nodes = head_selector('svelte-mv0rua', document.head);
			meta0 = claim_element(head_nodes, "META", { name: true, content: true });
			meta1 = claim_element(head_nodes, "META", { charset: true });
			link = claim_element(head_nodes, "LINK", { href: true, rel: true });
			style = claim_element(head_nodes, "STYLE", {});
			var style_nodes = children(style);
			t = claim_text(style_nodes, "@import url(\"https://unpkg.com/@primo-app/primo@1.3.64/reset.css\");\n\nhtml {\n  /* Colors */\n  --color-accent: #95B4BE;  \n  --font-primary: \"Bespoke Serif\", serif;\n  --font-secondary: system-ui, serif;\n\n  /* Default property values */\n  --background: white;\n  --color: #222;\n  --padding: 4rem 2rem;\n  --box-shadow: 0px 4px 30px rgba(0, 0, 0, 0.2);\n  --border-radius: 8px;\n  --max-width: 900px;\n  --border-color: #C6CCD2; \n  --transition-time: 0.1s;\n  --transition: var(--transition-time) color,\n    var(--transition-time) background-color,\n      var(--transition-time) border-color,\n        var(--transition-time) text-decoration-color,\n          var(--transition-time) box-shadow, var(--transtion-time) transform;\n}\n\n#page {\n  color: var(--color);\n  line-height: 1.6;\n  font-size: 1rem;\n  background: var(--background);\n}\n\n.section .content {\n  padding: var(--padding);\n  max-width: var(--max-width);\n  margin: 0 auto;\n}\n\n.section .content > * {\n    max-width: 700px;\n  }\n\n.section .content img {\n    width: 100%;\n    margin: 2rem 0;\n    box-shadow: var(--box-shadow);\n    border-radius: var(--border-radius);\n  }\n\n.section .content p {\n    padding: 0.5rem 0;\n    line-height: 1.5;\n  }\n\n.section .content a {\n\n  }\n\n.section .content h1 {\n    font-family: var(--font-primary);\n    font-size: 3rem;\n    font-weight: 700;\n    margin-bottom: 1rem;\n  }\n\n.section .content h2 {\n    font-family: var(--font-primary);\n    font-size: 1.75rem;\n    margin-bottom: 0.5rem;\n    font-weight: 500;\n\n   /* &:after {\n      width: 50px;\n      border-bottom: 3px solid var(--color);\n      content: \"\";\n      display: block;\n      margin-bottom: 1.5rem;\n      margin-top: 0.5rem;\n    }*/\n  }\n\n.section .content h3 {\n    font-family: var(--font-primary);\n    font-size: 1.5rem;\n    font-weight: 600;\n    margin-bottom: 0.25rem;\n  }\n\n.section .content ul {\n    list-style: disc;\n    padding: 0.5rem 0;\n    padding-left: 1.25rem;\n  }\n\n.section .content ol {\n    list-style: decimal;\n    padding: 0.5rem 0;\n    padding-left: 1.25rem;\n  }\n\n.section .content blockquote {\n    padding: 2rem;\n    box-shadow: var(--box-shadow);\n    border-radius: var(--border-radius);\n  }\n\n.section-container {\n  max-width: var(--max-width, 1200px);\n  margin: 0 auto;\n  padding: var(--padding); \n}\n\n.heading {\n  font-family: var(--font-primary);\n  font-size: 1.75rem; \n  line-height: 1;\n  font-weight: 500;\n  \n/*\n  &:after {\n    width: 50px;\n    border-bottom: 3px solid var(--color);\n    content: \"\";\n    display: block;\n    padding-top: 1rem;\n    margin-bottom: 1.5rem;\n  }\n  */\n}\n\n.link {\n  border-bottom: 1.5px solid #4C4E52;\n  transition: 0.1s border-color;\n}\n\n.link:hover {\n    border-color: transparent; \n  }\n\n.button {\n  color: white;\n  background: var(--color-accent);\n  border-radius: 5px;\n  padding: 8px 20px;\n  transition: var(--transition);\n}\n\n.button:hover {\n    box-shadow: 0 0 10px 5px rgba(0, 0, 0, 0.1);\n  }\n\n.button.inverted {\n    background: transparent;\n    color: var(--color-accent);\n    border: 2px solid var(--color-accent);\n  }");
			style_nodes.forEach(detach);
			head_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(meta0, "name", "viewport");
			attr(meta0, "content", "width=device-width, initial-scale=1.0");
			attr(meta1, "charset", "UTF-8");
			attr(link, "href", "https://api.fontshare.com/v2/css?f[]=bespoke-serif@400,700,401,500,501,701&display=swap");
			attr(link, "rel", "stylesheet");
		},
		m(target, anchor) {
			append_hydration(document.head, meta0);
			append_hydration(document.head, meta1);
			append_hydration(document.head, link);
			append_hydration(document.head, style);
			append_hydration(style, t);
		},
		p: noop,
		i: noop,
		o: noop,
		d(detaching) {
			detach(meta0);
			detach(meta1);
			detach(link);
			detach(style);
		}
	};
}

class Component extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, null, create_fragment, safe_not_equal, {});
	}
}

function cubicOut(t) {
    const f = t - 1.0;
    return f * f * f + 1.0;
}

function fade(node, { delay = 0, duration = 400, easing = identity } = {}) {
    const o = +getComputedStyle(node).opacity;
    return {
        delay,
        duration,
        easing,
        css: t => `opacity: ${t * o}`
    };
}
function slide(node, { delay = 0, duration = 400, easing = cubicOut, axis = 'y' } = {}) {
    const style = getComputedStyle(node);
    const opacity = +style.opacity;
    const primary_property = axis === 'y' ? 'height' : 'width';
    const primary_property_value = parseFloat(style[primary_property]);
    const secondary_properties = axis === 'y' ? ['top', 'bottom'] : ['left', 'right'];
    const capitalized_secondary_properties = secondary_properties.map((e) => `${e[0].toUpperCase()}${e.slice(1)}`);
    const padding_start_value = parseFloat(style[`padding${capitalized_secondary_properties[0]}`]);
    const padding_end_value = parseFloat(style[`padding${capitalized_secondary_properties[1]}`]);
    const margin_start_value = parseFloat(style[`margin${capitalized_secondary_properties[0]}`]);
    const margin_end_value = parseFloat(style[`margin${capitalized_secondary_properties[1]}`]);
    const border_width_start_value = parseFloat(style[`border${capitalized_secondary_properties[0]}Width`]);
    const border_width_end_value = parseFloat(style[`border${capitalized_secondary_properties[1]}Width`]);
    return {
        delay,
        duration,
        easing,
        css: t => 'overflow: hidden;' +
            `opacity: ${Math.min(t * 20, 1) * opacity};` +
            `${primary_property}: ${t * primary_property_value}px;` +
            `padding-${secondary_properties[0]}: ${t * padding_start_value}px;` +
            `padding-${secondary_properties[1]}: ${t * padding_end_value}px;` +
            `margin-${secondary_properties[0]}: ${t * margin_start_value}px;` +
            `margin-${secondary_properties[1]}: ${t * margin_end_value}px;` +
            `border-${secondary_properties[0]}-width: ${t * border_width_start_value}px;` +
            `border-${secondary_properties[1]}-width: ${t * border_width_end_value}px;`
    };
}

const matchIconName = /^[a-z0-9]+(-[a-z0-9]+)*$/;
const stringToIcon = (value, validate, allowSimpleName, provider = "") => {
  const colonSeparated = value.split(":");
  if (value.slice(0, 1) === "@") {
    if (colonSeparated.length < 2 || colonSeparated.length > 3) {
      return null;
    }
    provider = colonSeparated.shift().slice(1);
  }
  if (colonSeparated.length > 3 || !colonSeparated.length) {
    return null;
  }
  if (colonSeparated.length > 1) {
    const name2 = colonSeparated.pop();
    const prefix = colonSeparated.pop();
    const result = {
      provider: colonSeparated.length > 0 ? colonSeparated[0] : provider,
      prefix,
      name: name2
    };
    return validate && !validateIconName(result) ? null : result;
  }
  const name = colonSeparated[0];
  const dashSeparated = name.split("-");
  if (dashSeparated.length > 1) {
    const result = {
      provider,
      prefix: dashSeparated.shift(),
      name: dashSeparated.join("-")
    };
    return validate && !validateIconName(result) ? null : result;
  }
  if (allowSimpleName && provider === "") {
    const result = {
      provider,
      prefix: "",
      name
    };
    return validate && !validateIconName(result, allowSimpleName) ? null : result;
  }
  return null;
};
const validateIconName = (icon, allowSimpleName) => {
  if (!icon) {
    return false;
  }
  return !!((icon.provider === "" || icon.provider.match(matchIconName)) && (allowSimpleName && icon.prefix === "" || icon.prefix.match(matchIconName)) && icon.name.match(matchIconName));
};
const defaultIconDimensions = Object.freeze({
  left: 0,
  top: 0,
  width: 16,
  height: 16
});
const defaultIconTransformations = Object.freeze({
  rotate: 0,
  vFlip: false,
  hFlip: false
});
const defaultIconProps = Object.freeze({
  ...defaultIconDimensions,
  ...defaultIconTransformations
});
const defaultExtendedIconProps = Object.freeze({
  ...defaultIconProps,
  body: "",
  hidden: false
});
function mergeIconTransformations(obj1, obj2) {
  const result = {};
  if (!obj1.hFlip !== !obj2.hFlip) {
    result.hFlip = true;
  }
  if (!obj1.vFlip !== !obj2.vFlip) {
    result.vFlip = true;
  }
  const rotate = ((obj1.rotate || 0) + (obj2.rotate || 0)) % 4;
  if (rotate) {
    result.rotate = rotate;
  }
  return result;
}
function mergeIconData(parent, child) {
  const result = mergeIconTransformations(parent, child);
  for (const key in defaultExtendedIconProps) {
    if (key in defaultIconTransformations) {
      if (key in parent && !(key in result)) {
        result[key] = defaultIconTransformations[key];
      }
    } else if (key in child) {
      result[key] = child[key];
    } else if (key in parent) {
      result[key] = parent[key];
    }
  }
  return result;
}
function getIconsTree(data, names) {
  const icons = data.icons;
  const aliases = data.aliases || /* @__PURE__ */ Object.create(null);
  const resolved = /* @__PURE__ */ Object.create(null);
  function resolve(name) {
    if (icons[name]) {
      return resolved[name] = [];
    }
    if (!(name in resolved)) {
      resolved[name] = null;
      const parent = aliases[name] && aliases[name].parent;
      const value = parent && resolve(parent);
      if (value) {
        resolved[name] = [parent].concat(value);
      }
    }
    return resolved[name];
  }
  (names || Object.keys(icons).concat(Object.keys(aliases))).forEach(resolve);
  return resolved;
}
function internalGetIconData(data, name, tree) {
  const icons = data.icons;
  const aliases = data.aliases || /* @__PURE__ */ Object.create(null);
  let currentProps = {};
  function parse(name2) {
    currentProps = mergeIconData(icons[name2] || aliases[name2], currentProps);
  }
  parse(name);
  tree.forEach(parse);
  return mergeIconData(data, currentProps);
}
function parseIconSet(data, callback) {
  const names = [];
  if (typeof data !== "object" || typeof data.icons !== "object") {
    return names;
  }
  if (data.not_found instanceof Array) {
    data.not_found.forEach((name) => {
      callback(name, null);
      names.push(name);
    });
  }
  const tree = getIconsTree(data);
  for (const name in tree) {
    const item = tree[name];
    if (item) {
      callback(name, internalGetIconData(data, name, item));
      names.push(name);
    }
  }
  return names;
}
const optionalPropertyDefaults = {
  provider: "",
  aliases: {},
  not_found: {},
  ...defaultIconDimensions
};
function checkOptionalProps(item, defaults) {
  for (const prop in defaults) {
    if (prop in item && typeof item[prop] !== typeof defaults[prop]) {
      return false;
    }
  }
  return true;
}
function quicklyValidateIconSet(obj) {
  if (typeof obj !== "object" || obj === null) {
    return null;
  }
  const data = obj;
  if (typeof data.prefix !== "string" || !obj.icons || typeof obj.icons !== "object") {
    return null;
  }
  if (!checkOptionalProps(obj, optionalPropertyDefaults)) {
    return null;
  }
  const icons = data.icons;
  for (const name in icons) {
    const icon = icons[name];
    if (!name.match(matchIconName) || typeof icon.body !== "string" || !checkOptionalProps(icon, defaultExtendedIconProps)) {
      return null;
    }
  }
  const aliases = data.aliases || /* @__PURE__ */ Object.create(null);
  for (const name in aliases) {
    const icon = aliases[name];
    const parent = icon.parent;
    if (!name.match(matchIconName) || typeof parent !== "string" || !icons[parent] && !aliases[parent] || !checkOptionalProps(icon, defaultExtendedIconProps)) {
      return null;
    }
  }
  return data;
}
const dataStorage = /* @__PURE__ */ Object.create(null);
function newStorage(provider, prefix) {
  return {
    provider,
    prefix,
    icons: /* @__PURE__ */ Object.create(null),
    missing: /* @__PURE__ */ new Set()
  };
}
function getStorage(provider, prefix) {
  const providerStorage = dataStorage[provider] || (dataStorage[provider] = /* @__PURE__ */ Object.create(null));
  return providerStorage[prefix] || (providerStorage[prefix] = newStorage(provider, prefix));
}
function addIconSet(storage2, data) {
  if (!quicklyValidateIconSet(data)) {
    return [];
  }
  return parseIconSet(data, (name, icon) => {
    if (icon) {
      storage2.icons[name] = icon;
    } else {
      storage2.missing.add(name);
    }
  });
}
function addIconToStorage(storage2, name, icon) {
  try {
    if (typeof icon.body === "string") {
      storage2.icons[name] = {...icon};
      return true;
    }
  } catch (err) {
  }
  return false;
}
let simpleNames = false;
function allowSimpleNames(allow) {
  if (typeof allow === "boolean") {
    simpleNames = allow;
  }
  return simpleNames;
}
function getIconData(name) {
  const icon = typeof name === "string" ? stringToIcon(name, true, simpleNames) : name;
  if (icon) {
    const storage2 = getStorage(icon.provider, icon.prefix);
    const iconName = icon.name;
    return storage2.icons[iconName] || (storage2.missing.has(iconName) ? null : void 0);
  }
}
function addIcon(name, data) {
  const icon = stringToIcon(name, true, simpleNames);
  if (!icon) {
    return false;
  }
  const storage2 = getStorage(icon.provider, icon.prefix);
  return addIconToStorage(storage2, icon.name, data);
}
function addCollection(data, provider) {
  if (typeof data !== "object") {
    return false;
  }
  if (typeof provider !== "string") {
    provider = data.provider || "";
  }
  if (simpleNames && !provider && !data.prefix) {
    let added = false;
    if (quicklyValidateIconSet(data)) {
      data.prefix = "";
      parseIconSet(data, (name, icon) => {
        if (icon && addIcon(name, icon)) {
          added = true;
        }
      });
    }
    return added;
  }
  const prefix = data.prefix;
  if (!validateIconName({
    provider,
    prefix,
    name: "a"
  })) {
    return false;
  }
  const storage2 = getStorage(provider, prefix);
  return !!addIconSet(storage2, data);
}
const defaultIconSizeCustomisations = Object.freeze({
  width: null,
  height: null
});
const defaultIconCustomisations = Object.freeze({
  ...defaultIconSizeCustomisations,
  ...defaultIconTransformations
});
const unitsSplit = /(-?[0-9.]*[0-9]+[0-9.]*)/g;
const unitsTest = /^-?[0-9.]*[0-9]+[0-9.]*$/g;
function calculateSize(size, ratio, precision) {
  if (ratio === 1) {
    return size;
  }
  precision = precision || 100;
  if (typeof size === "number") {
    return Math.ceil(size * ratio * precision) / precision;
  }
  if (typeof size !== "string") {
    return size;
  }
  const oldParts = size.split(unitsSplit);
  if (oldParts === null || !oldParts.length) {
    return size;
  }
  const newParts = [];
  let code = oldParts.shift();
  let isNumber = unitsTest.test(code);
  while (true) {
    if (isNumber) {
      const num = parseFloat(code);
      if (isNaN(num)) {
        newParts.push(code);
      } else {
        newParts.push(Math.ceil(num * ratio * precision) / precision);
      }
    } else {
      newParts.push(code);
    }
    code = oldParts.shift();
    if (code === void 0) {
      return newParts.join("");
    }
    isNumber = !isNumber;
  }
}
const isUnsetKeyword = (value) => value === "unset" || value === "undefined" || value === "none";
function iconToSVG(icon, customisations) {
  const fullIcon = {
    ...defaultIconProps,
    ...icon
  };
  const fullCustomisations = {
    ...defaultIconCustomisations,
    ...customisations
  };
  const box = {
    left: fullIcon.left,
    top: fullIcon.top,
    width: fullIcon.width,
    height: fullIcon.height
  };
  let body = fullIcon.body;
  [fullIcon, fullCustomisations].forEach((props) => {
    const transformations = [];
    const hFlip = props.hFlip;
    const vFlip = props.vFlip;
    let rotation = props.rotate;
    if (hFlip) {
      if (vFlip) {
        rotation += 2;
      } else {
        transformations.push("translate(" + (box.width + box.left).toString() + " " + (0 - box.top).toString() + ")");
        transformations.push("scale(-1 1)");
        box.top = box.left = 0;
      }
    } else if (vFlip) {
      transformations.push("translate(" + (0 - box.left).toString() + " " + (box.height + box.top).toString() + ")");
      transformations.push("scale(1 -1)");
      box.top = box.left = 0;
    }
    let tempValue;
    if (rotation < 0) {
      rotation -= Math.floor(rotation / 4) * 4;
    }
    rotation = rotation % 4;
    switch (rotation) {
      case 1:
        tempValue = box.height / 2 + box.top;
        transformations.unshift("rotate(90 " + tempValue.toString() + " " + tempValue.toString() + ")");
        break;
      case 2:
        transformations.unshift("rotate(180 " + (box.width / 2 + box.left).toString() + " " + (box.height / 2 + box.top).toString() + ")");
        break;
      case 3:
        tempValue = box.width / 2 + box.left;
        transformations.unshift("rotate(-90 " + tempValue.toString() + " " + tempValue.toString() + ")");
        break;
    }
    if (rotation % 2 === 1) {
      if (box.left !== box.top) {
        tempValue = box.left;
        box.left = box.top;
        box.top = tempValue;
      }
      if (box.width !== box.height) {
        tempValue = box.width;
        box.width = box.height;
        box.height = tempValue;
      }
    }
    if (transformations.length) {
      body = '<g transform="' + transformations.join(" ") + '">' + body + "</g>";
    }
  });
  const customisationsWidth = fullCustomisations.width;
  const customisationsHeight = fullCustomisations.height;
  const boxWidth = box.width;
  const boxHeight = box.height;
  let width;
  let height;
  if (customisationsWidth === null) {
    height = customisationsHeight === null ? "1em" : customisationsHeight === "auto" ? boxHeight : customisationsHeight;
    width = calculateSize(height, boxWidth / boxHeight);
  } else {
    width = customisationsWidth === "auto" ? boxWidth : customisationsWidth;
    height = customisationsHeight === null ? calculateSize(width, boxHeight / boxWidth) : customisationsHeight === "auto" ? boxHeight : customisationsHeight;
  }
  const attributes = {};
  const setAttr = (prop, value) => {
    if (!isUnsetKeyword(value)) {
      attributes[prop] = value.toString();
    }
  };
  setAttr("width", width);
  setAttr("height", height);
  attributes.viewBox = box.left.toString() + " " + box.top.toString() + " " + boxWidth.toString() + " " + boxHeight.toString();
  return {
    attributes,
    body
  };
}
const regex = /\sid="(\S+)"/g;
const randomPrefix = "IconifyId" + Date.now().toString(16) + (Math.random() * 16777216 | 0).toString(16);
let counter = 0;
function replaceIDs(body, prefix = randomPrefix) {
  const ids = [];
  let match;
  while (match = regex.exec(body)) {
    ids.push(match[1]);
  }
  if (!ids.length) {
    return body;
  }
  const suffix = "suffix" + (Math.random() * 16777216 | Date.now()).toString(16);
  ids.forEach((id) => {
    const newID = typeof prefix === "function" ? prefix(id) : prefix + (counter++).toString();
    const escapedID = id.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
    body = body.replace(new RegExp('([#;"])(' + escapedID + ')([")]|\\.[a-z])', "g"), "$1" + newID + suffix + "$3");
  });
  body = body.replace(new RegExp(suffix, "g"), "");
  return body;
}
const storage = /* @__PURE__ */ Object.create(null);
function setAPIModule(provider, item) {
  storage[provider] = item;
}
function getAPIModule(provider) {
  return storage[provider] || storage[""];
}
function createAPIConfig(source) {
  let resources;
  if (typeof source.resources === "string") {
    resources = [source.resources];
  } else {
    resources = source.resources;
    if (!(resources instanceof Array) || !resources.length) {
      return null;
    }
  }
  const result = {
    resources,
    path: source.path || "/",
    maxURL: source.maxURL || 500,
    rotate: source.rotate || 750,
    timeout: source.timeout || 5e3,
    random: source.random === true,
    index: source.index || 0,
    dataAfterTimeout: source.dataAfterTimeout !== false
  };
  return result;
}
const configStorage = /* @__PURE__ */ Object.create(null);
const fallBackAPISources = [
  "https://api.simplesvg.com",
  "https://api.unisvg.com"
];
const fallBackAPI = [];
while (fallBackAPISources.length > 0) {
  if (fallBackAPISources.length === 1) {
    fallBackAPI.push(fallBackAPISources.shift());
  } else {
    if (Math.random() > 0.5) {
      fallBackAPI.push(fallBackAPISources.shift());
    } else {
      fallBackAPI.push(fallBackAPISources.pop());
    }
  }
}
configStorage[""] = createAPIConfig({
  resources: ["https://api.iconify.design"].concat(fallBackAPI)
});
function addAPIProvider(provider, customConfig) {
  const config = createAPIConfig(customConfig);
  if (config === null) {
    return false;
  }
  configStorage[provider] = config;
  return true;
}
function getAPIConfig(provider) {
  return configStorage[provider];
}
const detectFetch = () => {
  let callback;
  try {
    callback = fetch;
    if (typeof callback === "function") {
      return callback;
    }
  } catch (err) {
  }
};
let fetchModule = detectFetch();
function calculateMaxLength(provider, prefix) {
  const config = getAPIConfig(provider);
  if (!config) {
    return 0;
  }
  let result;
  if (!config.maxURL) {
    result = 0;
  } else {
    let maxHostLength = 0;
    config.resources.forEach((item) => {
      const host = item;
      maxHostLength = Math.max(maxHostLength, host.length);
    });
    const url = prefix + ".json?icons=";
    result = config.maxURL - maxHostLength - config.path.length - url.length;
  }
  return result;
}
function shouldAbort(status) {
  return status === 404;
}
const prepare = (provider, prefix, icons) => {
  const results = [];
  const maxLength = calculateMaxLength(provider, prefix);
  const type = "icons";
  let item = {
    type,
    provider,
    prefix,
    icons: []
  };
  let length = 0;
  icons.forEach((name, index) => {
    length += name.length + 1;
    if (length >= maxLength && index > 0) {
      results.push(item);
      item = {
        type,
        provider,
        prefix,
        icons: []
      };
      length = name.length;
    }
    item.icons.push(name);
  });
  results.push(item);
  return results;
};
function getPath(provider) {
  if (typeof provider === "string") {
    const config = getAPIConfig(provider);
    if (config) {
      return config.path;
    }
  }
  return "/";
}
const send = (host, params, callback) => {
  if (!fetchModule) {
    callback("abort", 424);
    return;
  }
  let path = getPath(params.provider);
  switch (params.type) {
    case "icons": {
      const prefix = params.prefix;
      const icons = params.icons;
      const iconsList = icons.join(",");
      const urlParams = new URLSearchParams({
        icons: iconsList
      });
      path += prefix + ".json?" + urlParams.toString();
      break;
    }
    case "custom": {
      const uri = params.uri;
      path += uri.slice(0, 1) === "/" ? uri.slice(1) : uri;
      break;
    }
    default:
      callback("abort", 400);
      return;
  }
  let defaultError = 503;
  fetchModule(host + path).then((response) => {
    const status = response.status;
    if (status !== 200) {
      setTimeout(() => {
        callback(shouldAbort(status) ? "abort" : "next", status);
      });
      return;
    }
    defaultError = 501;
    return response.json();
  }).then((data) => {
    if (typeof data !== "object" || data === null) {
      setTimeout(() => {
        if (data === 404) {
          callback("abort", data);
        } else {
          callback("next", defaultError);
        }
      });
      return;
    }
    setTimeout(() => {
      callback("success", data);
    });
  }).catch(() => {
    callback("next", defaultError);
  });
};
const fetchAPIModule = {
  prepare,
  send
};
function sortIcons(icons) {
  const result = {
    loaded: [],
    missing: [],
    pending: []
  };
  const storage2 = /* @__PURE__ */ Object.create(null);
  icons.sort((a, b) => {
    if (a.provider !== b.provider) {
      return a.provider.localeCompare(b.provider);
    }
    if (a.prefix !== b.prefix) {
      return a.prefix.localeCompare(b.prefix);
    }
    return a.name.localeCompare(b.name);
  });
  let lastIcon = {
    provider: "",
    prefix: "",
    name: ""
  };
  icons.forEach((icon) => {
    if (lastIcon.name === icon.name && lastIcon.prefix === icon.prefix && lastIcon.provider === icon.provider) {
      return;
    }
    lastIcon = icon;
    const provider = icon.provider;
    const prefix = icon.prefix;
    const name = icon.name;
    const providerStorage = storage2[provider] || (storage2[provider] = /* @__PURE__ */ Object.create(null));
    const localStorage = providerStorage[prefix] || (providerStorage[prefix] = getStorage(provider, prefix));
    let list;
    if (name in localStorage.icons) {
      list = result.loaded;
    } else if (prefix === "" || localStorage.missing.has(name)) {
      list = result.missing;
    } else {
      list = result.pending;
    }
    const item = {
      provider,
      prefix,
      name
    };
    list.push(item);
  });
  return result;
}
function removeCallback(storages, id) {
  storages.forEach((storage2) => {
    const items = storage2.loaderCallbacks;
    if (items) {
      storage2.loaderCallbacks = items.filter((row) => row.id !== id);
    }
  });
}
function updateCallbacks(storage2) {
  if (!storage2.pendingCallbacksFlag) {
    storage2.pendingCallbacksFlag = true;
    setTimeout(() => {
      storage2.pendingCallbacksFlag = false;
      const items = storage2.loaderCallbacks ? storage2.loaderCallbacks.slice(0) : [];
      if (!items.length) {
        return;
      }
      let hasPending = false;
      const provider = storage2.provider;
      const prefix = storage2.prefix;
      items.forEach((item) => {
        const icons = item.icons;
        const oldLength = icons.pending.length;
        icons.pending = icons.pending.filter((icon) => {
          if (icon.prefix !== prefix) {
            return true;
          }
          const name = icon.name;
          if (storage2.icons[name]) {
            icons.loaded.push({
              provider,
              prefix,
              name
            });
          } else if (storage2.missing.has(name)) {
            icons.missing.push({
              provider,
              prefix,
              name
            });
          } else {
            hasPending = true;
            return true;
          }
          return false;
        });
        if (icons.pending.length !== oldLength) {
          if (!hasPending) {
            removeCallback([storage2], item.id);
          }
          item.callback(icons.loaded.slice(0), icons.missing.slice(0), icons.pending.slice(0), item.abort);
        }
      });
    });
  }
}
let idCounter = 0;
function storeCallback(callback, icons, pendingSources) {
  const id = idCounter++;
  const abort = removeCallback.bind(null, pendingSources, id);
  if (!icons.pending.length) {
    return abort;
  }
  const item = {
    id,
    icons,
    callback,
    abort
  };
  pendingSources.forEach((storage2) => {
    (storage2.loaderCallbacks || (storage2.loaderCallbacks = [])).push(item);
  });
  return abort;
}
function listToIcons(list, validate = true, simpleNames2 = false) {
  const result = [];
  list.forEach((item) => {
    const icon = typeof item === "string" ? stringToIcon(item, validate, simpleNames2) : item;
    if (icon) {
      result.push(icon);
    }
  });
  return result;
}
var defaultConfig = {
  resources: [],
  index: 0,
  timeout: 2e3,
  rotate: 750,
  random: false,
  dataAfterTimeout: false
};
function sendQuery(config, payload, query, done) {
  const resourcesCount = config.resources.length;
  const startIndex = config.random ? Math.floor(Math.random() * resourcesCount) : config.index;
  let resources;
  if (config.random) {
    let list = config.resources.slice(0);
    resources = [];
    while (list.length > 1) {
      const nextIndex = Math.floor(Math.random() * list.length);
      resources.push(list[nextIndex]);
      list = list.slice(0, nextIndex).concat(list.slice(nextIndex + 1));
    }
    resources = resources.concat(list);
  } else {
    resources = config.resources.slice(startIndex).concat(config.resources.slice(0, startIndex));
  }
  const startTime = Date.now();
  let status = "pending";
  let queriesSent = 0;
  let lastError;
  let timer = null;
  let queue = [];
  let doneCallbacks = [];
  if (typeof done === "function") {
    doneCallbacks.push(done);
  }
  function resetTimer() {
    if (timer) {
      clearTimeout(timer);
      timer = null;
    }
  }
  function abort() {
    if (status === "pending") {
      status = "aborted";
    }
    resetTimer();
    queue.forEach((item) => {
      if (item.status === "pending") {
        item.status = "aborted";
      }
    });
    queue = [];
  }
  function subscribe(callback, overwrite) {
    if (overwrite) {
      doneCallbacks = [];
    }
    if (typeof callback === "function") {
      doneCallbacks.push(callback);
    }
  }
  function getQueryStatus() {
    return {
      startTime,
      payload,
      status,
      queriesSent,
      queriesPending: queue.length,
      subscribe,
      abort
    };
  }
  function failQuery() {
    status = "failed";
    doneCallbacks.forEach((callback) => {
      callback(void 0, lastError);
    });
  }
  function clearQueue() {
    queue.forEach((item) => {
      if (item.status === "pending") {
        item.status = "aborted";
      }
    });
    queue = [];
  }
  function moduleResponse(item, response, data) {
    const isError = response !== "success";
    queue = queue.filter((queued) => queued !== item);
    switch (status) {
      case "pending":
        break;
      case "failed":
        if (isError || !config.dataAfterTimeout) {
          return;
        }
        break;
      default:
        return;
    }
    if (response === "abort") {
      lastError = data;
      failQuery();
      return;
    }
    if (isError) {
      lastError = data;
      if (!queue.length) {
        if (!resources.length) {
          failQuery();
        } else {
          execNext();
        }
      }
      return;
    }
    resetTimer();
    clearQueue();
    if (!config.random) {
      const index = config.resources.indexOf(item.resource);
      if (index !== -1 && index !== config.index) {
        config.index = index;
      }
    }
    status = "completed";
    doneCallbacks.forEach((callback) => {
      callback(data);
    });
  }
  function execNext() {
    if (status !== "pending") {
      return;
    }
    resetTimer();
    const resource = resources.shift();
    if (resource === void 0) {
      if (queue.length) {
        timer = setTimeout(() => {
          resetTimer();
          if (status === "pending") {
            clearQueue();
            failQuery();
          }
        }, config.timeout);
        return;
      }
      failQuery();
      return;
    }
    const item = {
      status: "pending",
      resource,
      callback: (status2, data) => {
        moduleResponse(item, status2, data);
      }
    };
    queue.push(item);
    queriesSent++;
    timer = setTimeout(execNext, config.rotate);
    query(resource, payload, item.callback);
  }
  setTimeout(execNext);
  return getQueryStatus;
}
function initRedundancy(cfg) {
  const config = {
    ...defaultConfig,
    ...cfg
  };
  let queries = [];
  function cleanup() {
    queries = queries.filter((item) => item().status === "pending");
  }
  function query(payload, queryCallback, doneCallback) {
    const query2 = sendQuery(config, payload, queryCallback, (data, error) => {
      cleanup();
      if (doneCallback) {
        doneCallback(data, error);
      }
    });
    queries.push(query2);
    return query2;
  }
  function find(callback) {
    return queries.find((value) => {
      return callback(value);
    }) || null;
  }
  const instance = {
    query,
    find,
    setIndex: (index) => {
      config.index = index;
    },
    getIndex: () => config.index,
    cleanup
  };
  return instance;
}
function emptyCallback$1() {
}
const redundancyCache = /* @__PURE__ */ Object.create(null);
function getRedundancyCache(provider) {
  if (!redundancyCache[provider]) {
    const config = getAPIConfig(provider);
    if (!config) {
      return;
    }
    const redundancy = initRedundancy(config);
    const cachedReundancy = {
      config,
      redundancy
    };
    redundancyCache[provider] = cachedReundancy;
  }
  return redundancyCache[provider];
}
function sendAPIQuery(target, query, callback) {
  let redundancy;
  let send2;
  if (typeof target === "string") {
    const api = getAPIModule(target);
    if (!api) {
      callback(void 0, 424);
      return emptyCallback$1;
    }
    send2 = api.send;
    const cached = getRedundancyCache(target);
    if (cached) {
      redundancy = cached.redundancy;
    }
  } else {
    const config = createAPIConfig(target);
    if (config) {
      redundancy = initRedundancy(config);
      const moduleKey = target.resources ? target.resources[0] : "";
      const api = getAPIModule(moduleKey);
      if (api) {
        send2 = api.send;
      }
    }
  }
  if (!redundancy || !send2) {
    callback(void 0, 424);
    return emptyCallback$1;
  }
  return redundancy.query(query, send2, callback)().abort;
}
const browserCacheVersion = "iconify2";
const browserCachePrefix = "iconify";
const browserCacheCountKey = browserCachePrefix + "-count";
const browserCacheVersionKey = browserCachePrefix + "-version";
const browserStorageHour = 36e5;
const browserStorageCacheExpiration = 168;
function getStoredItem(func, key) {
  try {
    return func.getItem(key);
  } catch (err) {
  }
}
function setStoredItem(func, key, value) {
  try {
    func.setItem(key, value);
    return true;
  } catch (err) {
  }
}
function removeStoredItem(func, key) {
  try {
    func.removeItem(key);
  } catch (err) {
  }
}
function setBrowserStorageItemsCount(storage2, value) {
  return setStoredItem(storage2, browserCacheCountKey, value.toString());
}
function getBrowserStorageItemsCount(storage2) {
  return parseInt(getStoredItem(storage2, browserCacheCountKey)) || 0;
}
const browserStorageConfig = {
  local: true,
  session: true
};
const browserStorageEmptyItems = {
  local: /* @__PURE__ */ new Set(),
  session: /* @__PURE__ */ new Set()
};
let browserStorageStatus = false;
function setBrowserStorageStatus(status) {
  browserStorageStatus = status;
}
let _window = typeof window === "undefined" ? {} : window;
function getBrowserStorage(key) {
  const attr = key + "Storage";
  try {
    if (_window && _window[attr] && typeof _window[attr].length === "number") {
      return _window[attr];
    }
  } catch (err) {
  }
  browserStorageConfig[key] = false;
}
function iterateBrowserStorage(key, callback) {
  const func = getBrowserStorage(key);
  if (!func) {
    return;
  }
  const version = getStoredItem(func, browserCacheVersionKey);
  if (version !== browserCacheVersion) {
    if (version) {
      const total2 = getBrowserStorageItemsCount(func);
      for (let i = 0; i < total2; i++) {
        removeStoredItem(func, browserCachePrefix + i.toString());
      }
    }
    setStoredItem(func, browserCacheVersionKey, browserCacheVersion);
    setBrowserStorageItemsCount(func, 0);
    return;
  }
  const minTime = Math.floor(Date.now() / browserStorageHour) - browserStorageCacheExpiration;
  const parseItem = (index) => {
    const name = browserCachePrefix + index.toString();
    const item = getStoredItem(func, name);
    if (typeof item !== "string") {
      return;
    }
    try {
      const data = JSON.parse(item);
      if (typeof data === "object" && typeof data.cached === "number" && data.cached > minTime && typeof data.provider === "string" && typeof data.data === "object" && typeof data.data.prefix === "string" && callback(data, index)) {
        return true;
      }
    } catch (err) {
    }
    removeStoredItem(func, name);
  };
  let total = getBrowserStorageItemsCount(func);
  for (let i = total - 1; i >= 0; i--) {
    if (!parseItem(i)) {
      if (i === total - 1) {
        total--;
        setBrowserStorageItemsCount(func, total);
      } else {
        browserStorageEmptyItems[key].add(i);
      }
    }
  }
}
function initBrowserStorage() {
  if (browserStorageStatus) {
    return;
  }
  setBrowserStorageStatus(true);
  for (const key in browserStorageConfig) {
    iterateBrowserStorage(key, (item) => {
      const iconSet = item.data;
      const provider = item.provider;
      const prefix = iconSet.prefix;
      const storage2 = getStorage(provider, prefix);
      if (!addIconSet(storage2, iconSet).length) {
        return false;
      }
      const lastModified = iconSet.lastModified || -1;
      storage2.lastModifiedCached = storage2.lastModifiedCached ? Math.min(storage2.lastModifiedCached, lastModified) : lastModified;
      return true;
    });
  }
}
function updateLastModified(storage2, lastModified) {
  const lastValue = storage2.lastModifiedCached;
  if (lastValue && lastValue >= lastModified) {
    return lastValue === lastModified;
  }
  storage2.lastModifiedCached = lastModified;
  if (lastValue) {
    for (const key in browserStorageConfig) {
      iterateBrowserStorage(key, (item) => {
        const iconSet = item.data;
        return item.provider !== storage2.provider || iconSet.prefix !== storage2.prefix || iconSet.lastModified === lastModified;
      });
    }
  }
  return true;
}
function storeInBrowserStorage(storage2, data) {
  if (!browserStorageStatus) {
    initBrowserStorage();
  }
  function store(key) {
    let func;
    if (!browserStorageConfig[key] || !(func = getBrowserStorage(key))) {
      return;
    }
    const set = browserStorageEmptyItems[key];
    let index;
    if (set.size) {
      set.delete(index = Array.from(set).shift());
    } else {
      index = getBrowserStorageItemsCount(func);
      if (!setBrowserStorageItemsCount(func, index + 1)) {
        return;
      }
    }
    const item = {
      cached: Math.floor(Date.now() / browserStorageHour),
      provider: storage2.provider,
      data
    };
    return setStoredItem(func, browserCachePrefix + index.toString(), JSON.stringify(item));
  }
  if (data.lastModified && !updateLastModified(storage2, data.lastModified)) {
    return;
  }
  if (!Object.keys(data.icons).length) {
    return;
  }
  if (data.not_found) {
    data = Object.assign({}, data);
    delete data.not_found;
  }
  if (!store("local")) {
    store("session");
  }
}
function emptyCallback() {
}
function loadedNewIcons(storage2) {
  if (!storage2.iconsLoaderFlag) {
    storage2.iconsLoaderFlag = true;
    setTimeout(() => {
      storage2.iconsLoaderFlag = false;
      updateCallbacks(storage2);
    });
  }
}
function loadNewIcons(storage2, icons) {
  if (!storage2.iconsToLoad) {
    storage2.iconsToLoad = icons;
  } else {
    storage2.iconsToLoad = storage2.iconsToLoad.concat(icons).sort();
  }
  if (!storage2.iconsQueueFlag) {
    storage2.iconsQueueFlag = true;
    setTimeout(() => {
      storage2.iconsQueueFlag = false;
      const {provider, prefix} = storage2;
      const icons2 = storage2.iconsToLoad;
      delete storage2.iconsToLoad;
      let api;
      if (!icons2 || !(api = getAPIModule(provider))) {
        return;
      }
      const params = api.prepare(provider, prefix, icons2);
      params.forEach((item) => {
        sendAPIQuery(provider, item, (data) => {
          if (typeof data !== "object") {
            item.icons.forEach((name) => {
              storage2.missing.add(name);
            });
          } else {
            try {
              const parsed = addIconSet(storage2, data);
              if (!parsed.length) {
                return;
              }
              const pending = storage2.pendingIcons;
              if (pending) {
                parsed.forEach((name) => {
                  pending.delete(name);
                });
              }
              storeInBrowserStorage(storage2, data);
            } catch (err) {
              console.error(err);
            }
          }
          loadedNewIcons(storage2);
        });
      });
    });
  }
}
const loadIcons = (icons, callback) => {
  const cleanedIcons = listToIcons(icons, true, allowSimpleNames());
  const sortedIcons = sortIcons(cleanedIcons);
  if (!sortedIcons.pending.length) {
    let callCallback = true;
    if (callback) {
      setTimeout(() => {
        if (callCallback) {
          callback(sortedIcons.loaded, sortedIcons.missing, sortedIcons.pending, emptyCallback);
        }
      });
    }
    return () => {
      callCallback = false;
    };
  }
  const newIcons = /* @__PURE__ */ Object.create(null);
  const sources = [];
  let lastProvider, lastPrefix;
  sortedIcons.pending.forEach((icon) => {
    const {provider, prefix} = icon;
    if (prefix === lastPrefix && provider === lastProvider) {
      return;
    }
    lastProvider = provider;
    lastPrefix = prefix;
    sources.push(getStorage(provider, prefix));
    const providerNewIcons = newIcons[provider] || (newIcons[provider] = /* @__PURE__ */ Object.create(null));
    if (!providerNewIcons[prefix]) {
      providerNewIcons[prefix] = [];
    }
  });
  sortedIcons.pending.forEach((icon) => {
    const {provider, prefix, name} = icon;
    const storage2 = getStorage(provider, prefix);
    const pendingQueue = storage2.pendingIcons || (storage2.pendingIcons = /* @__PURE__ */ new Set());
    if (!pendingQueue.has(name)) {
      pendingQueue.add(name);
      newIcons[provider][prefix].push(name);
    }
  });
  sources.forEach((storage2) => {
    const {provider, prefix} = storage2;
    if (newIcons[provider][prefix].length) {
      loadNewIcons(storage2, newIcons[provider][prefix]);
    }
  });
  return callback ? storeCallback(callback, sortedIcons, sources) : emptyCallback;
};
function mergeCustomisations(defaults, item) {
  const result = {
    ...defaults
  };
  for (const key in item) {
    const value = item[key];
    const valueType = typeof value;
    if (key in defaultIconSizeCustomisations) {
      if (value === null || value && (valueType === "string" || valueType === "number")) {
        result[key] = value;
      }
    } else if (valueType === typeof result[key]) {
      result[key] = key === "rotate" ? value % 4 : value;
    }
  }
  return result;
}
const separator = /[\s,]+/;
function flipFromString(custom, flip) {
  flip.split(separator).forEach((str) => {
    const value = str.trim();
    switch (value) {
      case "horizontal":
        custom.hFlip = true;
        break;
      case "vertical":
        custom.vFlip = true;
        break;
    }
  });
}
function rotateFromString(value, defaultValue = 0) {
  const units = value.replace(/^-?[0-9.]*/, "");
  function cleanup(value2) {
    while (value2 < 0) {
      value2 += 4;
    }
    return value2 % 4;
  }
  if (units === "") {
    const num = parseInt(value);
    return isNaN(num) ? 0 : cleanup(num);
  } else if (units !== value) {
    let split = 0;
    switch (units) {
      case "%":
        split = 25;
        break;
      case "deg":
        split = 90;
    }
    if (split) {
      let num = parseFloat(value.slice(0, value.length - units.length));
      if (isNaN(num)) {
        return 0;
      }
      num = num / split;
      return num % 1 === 0 ? cleanup(num) : 0;
    }
  }
  return defaultValue;
}
function iconToHTML(body, attributes) {
  let renderAttribsHTML = body.indexOf("xlink:") === -1 ? "" : ' xmlns:xlink="http://www.w3.org/1999/xlink"';
  for (const attr in attributes) {
    renderAttribsHTML += " " + attr + '="' + attributes[attr] + '"';
  }
  return '<svg xmlns="http://www.w3.org/2000/svg"' + renderAttribsHTML + ">" + body + "</svg>";
}
function encodeSVGforURL(svg) {
  return svg.replace(/"/g, "'").replace(/%/g, "%25").replace(/#/g, "%23").replace(/</g, "%3C").replace(/>/g, "%3E").replace(/\s+/g, " ");
}
function svgToData(svg) {
  return "data:image/svg+xml," + encodeSVGforURL(svg);
}
function svgToURL(svg) {
  return 'url("' + svgToData(svg) + '")';
}
const defaultExtendedIconCustomisations = {
  ...defaultIconCustomisations,
  inline: false
};
const svgDefaults = {
  xmlns: "http://www.w3.org/2000/svg",
  "xmlns:xlink": "http://www.w3.org/1999/xlink",
  "aria-hidden": true,
  role: "img"
};
const commonProps = {
  display: "inline-block"
};
const monotoneProps = {
  "background-color": "currentColor"
};
const coloredProps = {
  "background-color": "transparent"
};
const propsToAdd = {
  image: "var(--svg)",
  repeat: "no-repeat",
  size: "100% 100%"
};
const propsToAddTo = {
  "-webkit-mask": monotoneProps,
  mask: monotoneProps,
  background: coloredProps
};
for (const prefix in propsToAddTo) {
  const list = propsToAddTo[prefix];
  for (const prop in propsToAdd) {
    list[prefix + "-" + prop] = propsToAdd[prop];
  }
}
function fixSize(value) {
  return value + (value.match(/^[-0-9.]+$/) ? "px" : "");
}
function render(icon, props) {
  const customisations = mergeCustomisations(defaultExtendedIconCustomisations, props);
  const mode = props.mode || "svg";
  const componentProps = mode === "svg" ? {...svgDefaults} : {};
  if (icon.body.indexOf("xlink:") === -1) {
    delete componentProps["xmlns:xlink"];
  }
  let style = typeof props.style === "string" ? props.style : "";
  for (let key in props) {
    const value = props[key];
    if (value === void 0) {
      continue;
    }
    switch (key) {
      case "icon":
      case "style":
      case "onLoad":
      case "mode":
        break;
      case "inline":
      case "hFlip":
      case "vFlip":
        customisations[key] = value === true || value === "true" || value === 1;
        break;
      case "flip":
        if (typeof value === "string") {
          flipFromString(customisations, value);
        }
        break;
      case "color":
        style = style + (style.length > 0 && style.trim().slice(-1) !== ";" ? ";" : "") + "color: " + value + "; ";
        break;
      case "rotate":
        if (typeof value === "string") {
          customisations[key] = rotateFromString(value);
        } else if (typeof value === "number") {
          customisations[key] = value;
        }
        break;
      case "ariaHidden":
      case "aria-hidden":
        if (value !== true && value !== "true") {
          delete componentProps["aria-hidden"];
        }
        break;
      default:
        if (key.slice(0, 3) === "on:") {
          break;
        }
        if (defaultExtendedIconCustomisations[key] === void 0) {
          componentProps[key] = value;
        }
    }
  }
  const item = iconToSVG(icon, customisations);
  const renderAttribs = item.attributes;
  if (customisations.inline) {
    style = "vertical-align: -0.125em; " + style;
  }
  if (mode === "svg") {
    Object.assign(componentProps, renderAttribs);
    if (style !== "") {
      componentProps.style = style;
    }
    let localCounter = 0;
    let id = props.id;
    if (typeof id === "string") {
      id = id.replace(/-/g, "_");
    }
    return {
      svg: true,
      attributes: componentProps,
      body: replaceIDs(item.body, id ? () => id + "ID" + localCounter++ : "iconifySvelte")
    };
  }
  const {body, width, height} = icon;
  const useMask = mode === "mask" || (mode === "bg" ? false : body.indexOf("currentColor") !== -1);
  const html = iconToHTML(body, {
    ...renderAttribs,
    width: width + "",
    height: height + ""
  });
  const url = svgToURL(html);
  const styles = {
    "--svg": url
  };
  const size = (prop) => {
    const value = renderAttribs[prop];
    if (value) {
      styles[prop] = fixSize(value);
    }
  };
  size("width");
  size("height");
  Object.assign(styles, commonProps, useMask ? monotoneProps : coloredProps);
  let customStyle = "";
  for (const key in styles) {
    customStyle += key + ": " + styles[key] + ";";
  }
  componentProps.style = customStyle + style;
  return {
    svg: false,
    attributes: componentProps
  };
}
allowSimpleNames(true);
setAPIModule("", fetchAPIModule);
if (typeof document !== "undefined" && typeof window !== "undefined") {
  initBrowserStorage();
  const _window2 = window;
  if (_window2.IconifyPreload !== void 0) {
    const preload = _window2.IconifyPreload;
    const err = "Invalid IconifyPreload syntax.";
    if (typeof preload === "object" && preload !== null) {
      (preload instanceof Array ? preload : [preload]).forEach((item) => {
        try {
          if (typeof item !== "object" || item === null || item instanceof Array || typeof item.icons !== "object" || typeof item.prefix !== "string" || !addCollection(item)) {
            console.error(err);
          }
        } catch (e) {
          console.error(err);
        }
      });
    }
  }
  if (_window2.IconifyProviders !== void 0) {
    const providers = _window2.IconifyProviders;
    if (typeof providers === "object" && providers !== null) {
      for (let key in providers) {
        const err = "IconifyProviders[" + key + "] is invalid.";
        try {
          const value = providers[key];
          if (typeof value !== "object" || !value || value.resources === void 0) {
            continue;
          }
          if (!addAPIProvider(key, value)) {
            console.error(err);
          }
        } catch (e) {
          console.error(err);
        }
      }
    }
  }
}
function checkIconState(icon, state, mounted, callback, onload) {
  function abortLoading() {
    if (state.loading) {
      state.loading.abort();
      state.loading = null;
    }
  }
  if (typeof icon === "object" && icon !== null && typeof icon.body === "string") {
    state.name = "";
    abortLoading();
    return {data: {...defaultIconProps, ...icon}};
  }
  let iconName;
  if (typeof icon !== "string" || (iconName = stringToIcon(icon, false, true)) === null) {
    abortLoading();
    return null;
  }
  const data = getIconData(iconName);
  if (!data) {
    if (mounted && (!state.loading || state.loading.name !== icon)) {
      abortLoading();
      state.name = "";
      state.loading = {
        name: icon,
        abort: loadIcons([iconName], callback)
      };
    }
    return null;
  }
  abortLoading();
  if (state.name !== icon) {
    state.name = icon;
    if (onload && !state.destroyed) {
      onload(icon);
    }
  }
  const classes = ["iconify"];
  if (iconName.prefix !== "") {
    classes.push("iconify--" + iconName.prefix);
  }
  if (iconName.provider !== "") {
    classes.push("iconify--" + iconName.provider);
  }
  return {data, classes};
}
function generateIcon(icon, props) {
  return icon ? render({
    ...defaultIconProps,
    ...icon
  }, props) : null;
}
var checkIconState_1 = checkIconState;
var generateIcon_1 = generateIcon;

/* generated by Svelte v3.58.0 */

function create_if_block(ctx) {
	let if_block_anchor;

	function select_block_type(ctx, dirty) {
		if (/*data*/ ctx[0].svg) return create_if_block_1;
		return create_else_block;
	}

	let current_block_type = select_block_type(ctx);
	let if_block = current_block_type(ctx);

	return {
		c() {
			if_block.c();
			if_block_anchor = empty();
		},
		l(nodes) {
			if_block.l(nodes);
			if_block_anchor = empty();
		},
		m(target, anchor) {
			if_block.m(target, anchor);
			insert_hydration(target, if_block_anchor, anchor);
		},
		p(ctx, dirty) {
			if (current_block_type === (current_block_type = select_block_type(ctx)) && if_block) {
				if_block.p(ctx, dirty);
			} else {
				if_block.d(1);
				if_block = current_block_type(ctx);

				if (if_block) {
					if_block.c();
					if_block.m(if_block_anchor.parentNode, if_block_anchor);
				}
			}
		},
		d(detaching) {
			if_block.d(detaching);
			if (detaching) detach(if_block_anchor);
		}
	};
}

// (113:1) {:else}
function create_else_block(ctx) {
	let span;
	let span_levels = [/*data*/ ctx[0].attributes];
	let span_data = {};

	for (let i = 0; i < span_levels.length; i += 1) {
		span_data = assign(span_data, span_levels[i]);
	}

	return {
		c() {
			span = element("span");
			this.h();
		},
		l(nodes) {
			span = claim_element(nodes, "SPAN", {});
			children(span).forEach(detach);
			this.h();
		},
		h() {
			set_attributes(span, span_data);
		},
		m(target, anchor) {
			insert_hydration(target, span, anchor);
		},
		p(ctx, dirty) {
			set_attributes(span, span_data = get_spread_update(span_levels, [dirty & /*data*/ 1 && /*data*/ ctx[0].attributes]));
		},
		d(detaching) {
			if (detaching) detach(span);
		}
	};
}

// (109:1) {#if data.svg}
function create_if_block_1(ctx) {
	let svg;
	let raw_value = /*data*/ ctx[0].body + "";
	let svg_levels = [/*data*/ ctx[0].attributes];
	let svg_data = {};

	for (let i = 0; i < svg_levels.length; i += 1) {
		svg_data = assign(svg_data, svg_levels[i]);
	}

	return {
		c() {
			svg = svg_element("svg");
			this.h();
		},
		l(nodes) {
			svg = claim_svg_element(nodes, "svg", {});
			var svg_nodes = children(svg);
			svg_nodes.forEach(detach);
			this.h();
		},
		h() {
			set_svg_attributes(svg, svg_data);
		},
		m(target, anchor) {
			insert_hydration(target, svg, anchor);
			svg.innerHTML = raw_value;
		},
		p(ctx, dirty) {
			if (dirty & /*data*/ 1 && raw_value !== (raw_value = /*data*/ ctx[0].body + "")) svg.innerHTML = raw_value;			set_svg_attributes(svg, svg_data = get_spread_update(svg_levels, [dirty & /*data*/ 1 && /*data*/ ctx[0].attributes]));
		},
		d(detaching) {
			if (detaching) detach(svg);
		}
	};
}

function create_fragment$1(ctx) {
	let if_block_anchor;
	let if_block = /*data*/ ctx[0] && create_if_block(ctx);

	return {
		c() {
			if (if_block) if_block.c();
			if_block_anchor = empty();
		},
		l(nodes) {
			if (if_block) if_block.l(nodes);
			if_block_anchor = empty();
		},
		m(target, anchor) {
			if (if_block) if_block.m(target, anchor);
			insert_hydration(target, if_block_anchor, anchor);
		},
		p(ctx, [dirty]) {
			if (/*data*/ ctx[0]) {
				if (if_block) {
					if_block.p(ctx, dirty);
				} else {
					if_block = create_if_block(ctx);
					if_block.c();
					if_block.m(if_block_anchor.parentNode, if_block_anchor);
				}
			} else if (if_block) {
				if_block.d(1);
				if_block = null;
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (if_block) if_block.d(detaching);
			if (detaching) detach(if_block_anchor);
		}
	};
}

function instance($$self, $$props, $$invalidate) {
	const state = {
		// Last icon name
		name: '',
		// Loading status
		loading: null,
		// Destroyed status
		destroyed: false
	};

	// Mounted status
	let mounted = false;

	// Callback counter
	let counter = 0;

	// Generated data
	let data;

	const onLoad = icon => {
		// Legacy onLoad property
		if (typeof $$props.onLoad === 'function') {
			$$props.onLoad(icon);
		}

		// on:load event
		const dispatch = createEventDispatcher();

		dispatch('load', { icon });
	};

	// Increase counter when loaded to force re-calculation of data
	function loaded() {
		$$invalidate(3, counter++, counter);
	}

	// Force re-render
	onMount(() => {
		$$invalidate(2, mounted = true);
	});

	// Abort loading when component is destroyed
	onDestroy(() => {
		$$invalidate(1, state.destroyed = true, state);

		if (state.loading) {
			state.loading.abort();
			$$invalidate(1, state.loading = null, state);
		}
	});

	$$self.$$set = $$new_props => {
		$$invalidate(6, $$props = assign(assign({}, $$props), exclude_internal_props($$new_props)));
	};

	$$self.$$.update = () => {
		 {
			const iconData = checkIconState_1($$props.icon, state, mounted, loaded, onLoad);
			$$invalidate(0, data = iconData ? generateIcon_1(iconData.data, $$props) : null);

			if (data && iconData.classes) {
				// Add classes
				$$invalidate(
					0,
					data.attributes['class'] = (typeof $$props['class'] === 'string'
					? $$props['class'] + ' '
					: '') + iconData.classes.join(' '),
					data
				);
			}
		}
	};

	$$props = exclude_internal_props($$props);
	return [data, state, mounted, counter];
}

class Component$1 extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance, create_fragment$1, safe_not_equal, {});
	}
}

/* generated by Svelte v3.58.0 */

function get_each_context(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[6] = list[i].link;
	return child_ctx;
}

function get_each_context_1(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[6] = list[i].link;
	return child_ctx;
}

// (114:6) {#each site_nav as { link }}
function create_each_block_1(ctx) {
	let a;
	let t_value = /*link*/ ctx[6].label + "";
	let t;
	let a_href_value;

	return {
		c() {
			a = element("a");
			t = text(t_value);
			this.h();
		},
		l(nodes) {
			a = claim_element(nodes, "A", { class: true, href: true });
			var a_nodes = children(a);
			t = claim_text(a_nodes, t_value);
			a_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "class", "link svelte-exauqk");
			attr(a, "href", a_href_value = /*link*/ ctx[6].url);
			toggle_class(a, "active", /*link*/ ctx[6].url === window.location.pathname);
		},
		m(target, anchor) {
			insert_hydration(target, a, anchor);
			append_hydration(a, t);
		},
		p(ctx, dirty) {
			if (dirty & /*site_nav*/ 1 && t_value !== (t_value = /*link*/ ctx[6].label + "")) set_data(t, t_value);

			if (dirty & /*site_nav*/ 1 && a_href_value !== (a_href_value = /*link*/ ctx[6].url)) {
				attr(a, "href", a_href_value);
			}

			if (dirty & /*site_nav, window*/ 1) {
				toggle_class(a, "active", /*link*/ ctx[6].url === window.location.pathname);
			}
		},
		d(detaching) {
			if (detaching) detach(a);
		}
	};
}

// (126:4) {#if mobileNavOpen}
function create_if_block$1(ctx) {
	let nav;
	let t;
	let button;
	let icon;
	let nav_transition;
	let current;
	let mounted;
	let dispose;
	let each_value = /*site_nav*/ ctx[0];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block(get_each_context(ctx, each_value, i));
	}

	icon = new Component$1({ props: { height: "25", icon: "bi:x-lg" } });

	return {
		c() {
			nav = element("nav");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			t = space();
			button = element("button");
			create_component(icon.$$.fragment);
			this.h();
		},
		l(nodes) {
			nav = claim_element(nodes, "NAV", { id: true, class: true });
			var nav_nodes = children(nav);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(nav_nodes);
			}

			t = claim_space(nav_nodes);

			button = claim_element(nav_nodes, "BUTTON", {
				id: true,
				"aria-label": true,
				class: true
			});

			var button_nodes = children(button);
			claim_component(icon.$$.fragment, button_nodes);
			button_nodes.forEach(detach);
			nav_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(button, "id", "close");
			attr(button, "aria-label", "Close Navigation");
			attr(button, "class", "svelte-exauqk");
			attr(nav, "id", "popup");
			attr(nav, "class", "svelte-exauqk");
		},
		m(target, anchor) {
			insert_hydration(target, nav, anchor);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(nav, null);
				}
			}

			append_hydration(nav, t);
			append_hydration(nav, button);
			mount_component(icon, button, null);
			current = true;

			if (!mounted) {
				dispose = listen(button, "click", /*click_handler_1*/ ctx[4]);
				mounted = true;
			}
		},
		p(ctx, dirty) {
			if (dirty & /*site_nav, window*/ 1) {
				each_value = /*site_nav*/ ctx[0];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(nav, t);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value.length;
			}
		},
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);

			add_render_callback(() => {
				if (!current) return;
				if (!nav_transition) nav_transition = create_bidirectional_transition(nav, fade, { duration: 200 }, true);
				nav_transition.run(1);
			});

			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			if (!nav_transition) nav_transition = create_bidirectional_transition(nav, fade, { duration: 200 }, false);
			nav_transition.run(0);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(nav);
			destroy_each(each_blocks, detaching);
			destroy_component(icon);
			if (detaching && nav_transition) nav_transition.end();
			mounted = false;
			dispose();
		}
	};
}

// (128:8) {#each site_nav as { link }}
function create_each_block(ctx) {
	let a;
	let t_value = /*link*/ ctx[6].label + "";
	let t;
	let a_href_value;

	return {
		c() {
			a = element("a");
			t = text(t_value);
			this.h();
		},
		l(nodes) {
			a = claim_element(nodes, "A", { href: true });
			var a_nodes = children(a);
			t = claim_text(a_nodes, t_value);
			a_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "href", a_href_value = /*link*/ ctx[6].url);
			toggle_class(a, "active", /*link*/ ctx[6].url === window.location.pathname);
		},
		m(target, anchor) {
			insert_hydration(target, a, anchor);
			append_hydration(a, t);
		},
		p(ctx, dirty) {
			if (dirty & /*site_nav*/ 1 && t_value !== (t_value = /*link*/ ctx[6].label + "")) set_data(t, t_value);

			if (dirty & /*site_nav*/ 1 && a_href_value !== (a_href_value = /*link*/ ctx[6].url)) {
				attr(a, "href", a_href_value);
			}

			if (dirty & /*site_nav, window*/ 1) {
				toggle_class(a, "active", /*link*/ ctx[6].url === window.location.pathname);
			}
		},
		d(detaching) {
			if (detaching) detach(a);
		}
	};
}

function create_fragment$2(ctx) {
	let div4;
	let div3;
	let header;
	let div0;
	let nav;
	let t0;
	let div1;
	let button;
	let icon;
	let t1;
	let t2;
	let div2;
	let hr;
	let current;
	let mounted;
	let dispose;
	let each_value_1 = /*site_nav*/ ctx[0];
	let each_blocks = [];

	for (let i = 0; i < each_value_1.length; i += 1) {
		each_blocks[i] = create_each_block_1(get_each_context_1(ctx, each_value_1, i));
	}

	icon = new Component$1({
			props: { height: "30", icon: "eva:menu-outline" }
		});

	let if_block = /*mobileNavOpen*/ ctx[1] && create_if_block$1(ctx);

	return {
		c() {
			div4 = element("div");
			div3 = element("div");
			header = element("header");
			div0 = element("div");
			nav = element("nav");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			t0 = space();
			div1 = element("div");
			button = element("button");
			create_component(icon.$$.fragment);
			t1 = space();
			if (if_block) if_block.c();
			t2 = space();
			div2 = element("div");
			hr = element("hr");
			this.h();
		},
		l(nodes) {
			div4 = claim_element(nodes, "DIV", { class: true, id: true });
			var div4_nodes = children(div4);
			div3 = claim_element(div4_nodes, "DIV", { class: true });
			var div3_nodes = children(div3);
			header = claim_element(div3_nodes, "HEADER", { class: true });
			var header_nodes = children(header);
			div0 = claim_element(header_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			nav = claim_element(div0_nodes, "NAV", { class: true });
			var nav_nodes = children(nav);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(nav_nodes);
			}

			nav_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			t0 = claim_space(header_nodes);
			div1 = claim_element(header_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			button = claim_element(div1_nodes, "BUTTON", { id: true, "aria-label": true });
			var button_nodes = children(button);
			claim_component(icon.$$.fragment, button_nodes);
			button_nodes.forEach(detach);
			t1 = claim_space(div1_nodes);
			if (if_block) if_block.l(div1_nodes);
			div1_nodes.forEach(detach);
			header_nodes.forEach(detach);
			t2 = claim_space(div3_nodes);
			div2 = claim_element(div3_nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			hr = claim_element(div2_nodes, "HR", { class: true });
			div2_nodes.forEach(detach);
			div3_nodes.forEach(detach);
			div4_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(nav, "class", "svelte-exauqk");
			attr(div0, "class", "desktop-nav svelte-exauqk");
			attr(button, "id", "open");
			attr(button, "aria-label", "Open mobile navigation");
			attr(div1, "class", "mobile-nav svelte-exauqk");
			attr(header, "class", "section-container svelte-exauqk");
			attr(hr, "class", "svelte-exauqk");
			attr(div2, "class", "section-container bottom svelte-exauqk");
			attr(div3, "class", "component");
			attr(div4, "class", "section");
			attr(div4, "id", "section-2969b5aa-7ab5-4790-9da7-57794870784d");
		},
		m(target, anchor) {
			insert_hydration(target, div4, anchor);
			append_hydration(div4, div3);
			append_hydration(div3, header);
			append_hydration(header, div0);
			append_hydration(div0, nav);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(nav, null);
				}
			}

			append_hydration(header, t0);
			append_hydration(header, div1);
			append_hydration(div1, button);
			mount_component(icon, button, null);
			append_hydration(div1, t1);
			if (if_block) if_block.m(div1, null);
			append_hydration(div3, t2);
			append_hydration(div3, div2);
			append_hydration(div2, hr);
			current = true;

			if (!mounted) {
				dispose = listen(button, "click", /*click_handler*/ ctx[3]);
				mounted = true;
			}
		},
		p(ctx, [dirty]) {
			if (dirty & /*site_nav, window*/ 1) {
				each_value_1 = /*site_nav*/ ctx[0];
				let i;

				for (i = 0; i < each_value_1.length; i += 1) {
					const child_ctx = get_each_context_1(ctx, each_value_1, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block_1(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(nav, null);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value_1.length;
			}

			if (/*mobileNavOpen*/ ctx[1]) {
				if (if_block) {
					if_block.p(ctx, dirty);

					if (dirty & /*mobileNavOpen*/ 2) {
						transition_in(if_block, 1);
					}
				} else {
					if_block = create_if_block$1(ctx);
					if_block.c();
					transition_in(if_block, 1);
					if_block.m(div1, null);
				}
			} else if (if_block) {
				group_outros();

				transition_out(if_block, 1, 1, () => {
					if_block = null;
				});

				check_outros();
			}
		},
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);
			transition_in(if_block);
			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			transition_out(if_block);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(div4);
			destroy_each(each_blocks, detaching);
			destroy_component(icon);
			if (if_block) if_block.d();
			mounted = false;
			dispose();
		}
	};
}

function instance$1($$self, $$props, $$invalidate) {
	let { logo } = $$props;
	let { site_nav } = $$props;
	let mobileNavOpen = false;

	const click_handler = () => $$invalidate(1, mobileNavOpen = true);
	const click_handler_1 = () => $$invalidate(1, mobileNavOpen = false);

	$$self.$$set = $$props => {
		if ('logo' in $$props) $$invalidate(2, logo = $$props.logo);
		if ('site_nav' in $$props) $$invalidate(0, site_nav = $$props.site_nav);
	};

	return [site_nav, mobileNavOpen, logo, click_handler, click_handler_1];
}

class Component$2 extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$1, create_fragment$2, safe_not_equal, { logo: 2, site_nav: 0 });
	}
}

/* generated by Svelte v3.58.0 */

function get_each_context$1(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[6] = list[i].link;
	child_ctx[7] = list[i].icon;
	return child_ctx;
}

// (139:2) {#if portrait.url}
function create_if_block_1$1(ctx) {
	let figure;
	let img;
	let img_src_value;
	let img_alt_value;
	let t;
	let svg;
	let circle0;
	let circle1;
	let circle2;
	let mounted;
	let dispose;

	return {
		c() {
			figure = element("figure");
			img = element("img");
			t = space();
			svg = svg_element("svg");
			circle0 = svg_element("circle");
			circle1 = svg_element("circle");
			circle2 = svg_element("circle");
			this.h();
		},
		l(nodes) {
			figure = claim_element(nodes, "FIGURE", { class: true });
			var figure_nodes = children(figure);
			img = claim_element(figure_nodes, "IMG", { src: true, alt: true, class: true });
			t = claim_space(figure_nodes);
			svg = claim_svg_element(figure_nodes, "svg", { height: true, width: true, class: true });
			var svg_nodes = children(svg);
			circle0 = claim_svg_element(svg_nodes, "circle", { cx: true, cy: true, r: true, class: true });
			children(circle0).forEach(detach);
			circle1 = claim_svg_element(svg_nodes, "circle", { cx: true, cy: true, r: true, class: true });
			children(circle1).forEach(detach);
			circle2 = claim_svg_element(svg_nodes, "circle", { cx: true, cy: true, r: true, class: true });
			children(circle2).forEach(detach);
			svg_nodes.forEach(detach);
			figure_nodes.forEach(detach);
			this.h();
		},
		h() {
			if (!src_url_equal(img.src, img_src_value = /*portrait*/ ctx[0].url)) attr(img, "src", img_src_value);
			attr(img, "alt", img_alt_value = /*portrait*/ ctx[0].alt);
			attr(img, "class", "svelte-16fkkfp");
			attr(circle0, "cx", "131");
			attr(circle0, "cy", "113");
			attr(circle0, "r", "113");
			attr(circle0, "class", "svelte-16fkkfp");
			attr(circle1, "cx", "131");
			attr(circle1, "cy", "113");
			attr(circle1, "r", "113");
			attr(circle1, "class", "svelte-16fkkfp");
			attr(circle2, "cx", "131");
			attr(circle2, "cy", "113");
			attr(circle2, "r", "113");
			attr(circle2, "class", "svelte-16fkkfp");
			attr(svg, "height", "226");
			attr(svg, "width", "226");
			attr(svg, "class", "svelte-16fkkfp");
			toggle_class(svg, "show", /*imageLoaded*/ ctx[4]);
			attr(figure, "class", "svelte-16fkkfp");
		},
		m(target, anchor) {
			insert_hydration(target, figure, anchor);
			append_hydration(figure, img);
			append_hydration(figure, t);
			append_hydration(figure, svg);
			append_hydration(svg, circle0);
			append_hydration(svg, circle1);
			append_hydration(svg, circle2);

			if (!mounted) {
				dispose = listen(img, "load", /*load_handler*/ ctx[5]);
				mounted = true;
			}
		},
		p(ctx, dirty) {
			if (dirty & /*portrait*/ 1 && !src_url_equal(img.src, img_src_value = /*portrait*/ ctx[0].url)) {
				attr(img, "src", img_src_value);
			}

			if (dirty & /*portrait*/ 1 && img_alt_value !== (img_alt_value = /*portrait*/ ctx[0].alt)) {
				attr(img, "alt", img_alt_value);
			}

			if (dirty & /*imageLoaded*/ 16) {
				toggle_class(svg, "show", /*imageLoaded*/ ctx[4]);
			}
		},
		d(detaching) {
			if (detaching) detach(figure);
			mounted = false;
			dispose();
		}
	};
}

// (168:10) {#if icon}
function create_if_block$2(ctx) {
	let span;
	let icon;
	let current;
	icon = new Component$1({ props: { icon: /*icon*/ ctx[7] } });

	return {
		c() {
			span = element("span");
			create_component(icon.$$.fragment);
			this.h();
		},
		l(nodes) {
			span = claim_element(nodes, "SPAN", { class: true });
			var span_nodes = children(span);
			claim_component(icon.$$.fragment, span_nodes);
			span_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(span, "class", "icon svelte-16fkkfp");
		},
		m(target, anchor) {
			insert_hydration(target, span, anchor);
			mount_component(icon, span, null);
			current = true;
		},
		p(ctx, dirty) {
			const icon_changes = {};
			if (dirty & /*social_links*/ 8) icon_changes.icon = /*icon*/ ctx[7];
			icon.$set(icon_changes);
		},
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(span);
			destroy_component(icon);
		}
	};
}

// (165:6) {#each social_links as {link, icon}}
function create_each_block$1(ctx) {
	let li;
	let a;
	let t0;
	let span;
	let t1_value = /*link*/ ctx[6].label + "";
	let t1;
	let a_href_value;
	let t2;
	let current;
	let if_block = /*icon*/ ctx[7] && create_if_block$2(ctx);

	return {
		c() {
			li = element("li");
			a = element("a");
			if (if_block) if_block.c();
			t0 = space();
			span = element("span");
			t1 = text(t1_value);
			t2 = space();
			this.h();
		},
		l(nodes) {
			li = claim_element(nodes, "LI", { class: true });
			var li_nodes = children(li);
			a = claim_element(li_nodes, "A", { href: true, class: true });
			var a_nodes = children(a);
			if (if_block) if_block.l(a_nodes);
			t0 = claim_space(a_nodes);
			span = claim_element(a_nodes, "SPAN", {});
			var span_nodes = children(span);
			t1 = claim_text(span_nodes, t1_value);
			span_nodes.forEach(detach);
			a_nodes.forEach(detach);
			t2 = claim_space(li_nodes);
			li_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "href", a_href_value = /*link*/ ctx[6].url);
			attr(a, "class", "svelte-16fkkfp");
			attr(li, "class", "svelte-16fkkfp");
		},
		m(target, anchor) {
			insert_hydration(target, li, anchor);
			append_hydration(li, a);
			if (if_block) if_block.m(a, null);
			append_hydration(a, t0);
			append_hydration(a, span);
			append_hydration(span, t1);
			append_hydration(li, t2);
			current = true;
		},
		p(ctx, dirty) {
			if (/*icon*/ ctx[7]) {
				if (if_block) {
					if_block.p(ctx, dirty);

					if (dirty & /*social_links*/ 8) {
						transition_in(if_block, 1);
					}
				} else {
					if_block = create_if_block$2(ctx);
					if_block.c();
					transition_in(if_block, 1);
					if_block.m(a, t0);
				}
			} else if (if_block) {
				group_outros();

				transition_out(if_block, 1, 1, () => {
					if_block = null;
				});

				check_outros();
			}

			if ((!current || dirty & /*social_links*/ 8) && t1_value !== (t1_value = /*link*/ ctx[6].label + "")) set_data(t1, t1_value);

			if (!current || dirty & /*social_links*/ 8 && a_href_value !== (a_href_value = /*link*/ ctx[6].url)) {
				attr(a, "href", a_href_value);
			}
		},
		i(local) {
			if (current) return;
			transition_in(if_block);
			current = true;
		},
		o(local) {
			transition_out(if_block);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(li);
			if (if_block) if_block.d();
		}
	};
}

function create_fragment$3(ctx) {
	let div4;
	let div3;
	let div2;
	let t0;
	let div1;
	let h1;
	let t1;
	let t2;
	let div0;
	let raw_value = /*description*/ ctx[2].html + "";
	let t3;
	let ul;
	let current;
	let if_block = /*portrait*/ ctx[0].url && create_if_block_1$1(ctx);
	let each_value = /*social_links*/ ctx[3];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block$1(get_each_context$1(ctx, each_value, i));
	}

	const out = i => transition_out(each_blocks[i], 1, 1, () => {
		each_blocks[i] = null;
	});

	return {
		c() {
			div4 = element("div");
			div3 = element("div");
			div2 = element("div");
			if (if_block) if_block.c();
			t0 = space();
			div1 = element("div");
			h1 = element("h1");
			t1 = text(/*name*/ ctx[1]);
			t2 = space();
			div0 = element("div");
			t3 = space();
			ul = element("ul");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			this.h();
		},
		l(nodes) {
			div4 = claim_element(nodes, "DIV", { class: true, id: true });
			var div4_nodes = children(div4);
			div3 = claim_element(div4_nodes, "DIV", { class: true });
			var div3_nodes = children(div3);
			div2 = claim_element(div3_nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			if (if_block) if_block.l(div2_nodes);
			t0 = claim_space(div2_nodes);
			div1 = claim_element(div2_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			h1 = claim_element(div1_nodes, "H1", { class: true });
			var h1_nodes = children(h1);
			t1 = claim_text(h1_nodes, /*name*/ ctx[1]);
			h1_nodes.forEach(detach);
			t2 = claim_space(div1_nodes);
			div0 = claim_element(div1_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			div0_nodes.forEach(detach);
			t3 = claim_space(div1_nodes);
			ul = claim_element(div1_nodes, "UL", { class: true });
			var ul_nodes = children(ul);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(ul_nodes);
			}

			ul_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			div3_nodes.forEach(detach);
			div4_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h1, "class", "heading svelte-16fkkfp");
			attr(div0, "class", "description svelte-16fkkfp");
			attr(ul, "class", "social svelte-16fkkfp");
			attr(div1, "class", "svelte-16fkkfp");
			attr(div2, "class", "section-container svelte-16fkkfp");
			attr(div3, "class", "component");
			attr(div4, "class", "section");
			attr(div4, "id", "section-11d2fcde-7759-4dde-a53b-1667fd96b13c");
		},
		m(target, anchor) {
			insert_hydration(target, div4, anchor);
			append_hydration(div4, div3);
			append_hydration(div3, div2);
			if (if_block) if_block.m(div2, null);
			append_hydration(div2, t0);
			append_hydration(div2, div1);
			append_hydration(div1, h1);
			append_hydration(h1, t1);
			append_hydration(div1, t2);
			append_hydration(div1, div0);
			div0.innerHTML = raw_value;
			append_hydration(div1, t3);
			append_hydration(div1, ul);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(ul, null);
				}
			}

			current = true;
		},
		p(ctx, [dirty]) {
			if (/*portrait*/ ctx[0].url) {
				if (if_block) {
					if_block.p(ctx, dirty);
				} else {
					if_block = create_if_block_1$1(ctx);
					if_block.c();
					if_block.m(div2, t0);
				}
			} else if (if_block) {
				if_block.d(1);
				if_block = null;
			}

			if (!current || dirty & /*name*/ 2) set_data(t1, /*name*/ ctx[1]);
			if ((!current || dirty & /*description*/ 4) && raw_value !== (raw_value = /*description*/ ctx[2].html + "")) div0.innerHTML = raw_value;
			if (dirty & /*social_links*/ 8) {
				each_value = /*social_links*/ ctx[3];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context$1(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
						transition_in(each_blocks[i], 1);
					} else {
						each_blocks[i] = create_each_block$1(child_ctx);
						each_blocks[i].c();
						transition_in(each_blocks[i], 1);
						each_blocks[i].m(ul, null);
					}
				}

				group_outros();

				for (i = each_value.length; i < each_blocks.length; i += 1) {
					out(i);
				}

				check_outros();
			}
		},
		i(local) {
			if (current) return;

			for (let i = 0; i < each_value.length; i += 1) {
				transition_in(each_blocks[i]);
			}

			current = true;
		},
		o(local) {
			each_blocks = each_blocks.filter(Boolean);

			for (let i = 0; i < each_blocks.length; i += 1) {
				transition_out(each_blocks[i]);
			}

			current = false;
		},
		d(detaching) {
			if (detaching) detach(div4);
			if (if_block) if_block.d();
			destroy_each(each_blocks, detaching);
		}
	};
}

function instance$2($$self, $$props, $$invalidate) {
	let { portrait } = $$props;
	let { name } = $$props;
	let { description } = $$props;
	let { social_links } = $$props;
	let imageLoaded = false;
	const load_handler = () => $$invalidate(4, imageLoaded = true);

	$$self.$$set = $$props => {
		if ('portrait' in $$props) $$invalidate(0, portrait = $$props.portrait);
		if ('name' in $$props) $$invalidate(1, name = $$props.name);
		if ('description' in $$props) $$invalidate(2, description = $$props.description);
		if ('social_links' in $$props) $$invalidate(3, social_links = $$props.social_links);
	};

	return [portrait, name, description, social_links, imageLoaded, load_handler];
}

class Component$3 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$2, create_fragment$3, safe_not_equal, {
			portrait: 0,
			name: 1,
			description: 2,
			social_links: 3
		});
	}
}

/* generated by Svelte v3.58.0 */

function create_fragment$4(ctx) {
	let div3;
	let div2;
	let div1;
	let div0;
	let raw_value = /*content*/ ctx[0].html + "";

	return {
		c() {
			div3 = element("div");
			div2 = element("div");
			div1 = element("div");
			div0 = element("div");
			this.h();
		},
		l(nodes) {
			div3 = claim_element(nodes, "DIV", { class: true, id: true });
			var div3_nodes = children(div3);
			div2 = claim_element(div3_nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			div1 = claim_element(div2_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			div0 = claim_element(div1_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			div0_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			div3_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(div0, "class", "section-container content svelte-1nam8hy");
			attr(div1, "class", "section");
			attr(div2, "class", "component");
			attr(div3, "class", "section");
			attr(div3, "id", "section-1042c66d-10f3-4caf-8bd6-c318d2c2f1fb");
		},
		m(target, anchor) {
			insert_hydration(target, div3, anchor);
			append_hydration(div3, div2);
			append_hydration(div2, div1);
			append_hydration(div1, div0);
			div0.innerHTML = raw_value;
		},
		p(ctx, [dirty]) {
			if (dirty & /*content*/ 1 && raw_value !== (raw_value = /*content*/ ctx[0].html + "")) div0.innerHTML = raw_value;		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div3);
		}
	};
}

function instance$3($$self, $$props, $$invalidate) {
	let { content } = $$props;

	$$self.$$set = $$props => {
		if ('content' in $$props) $$invalidate(0, content = $$props.content);
	};

	return [content];
}

class Component$4 extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$3, create_fragment$4, safe_not_equal, { content: 0 });
	}
}

/* generated by Svelte v3.58.0 */

function get_each_context$2(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[6] = list[i];
	return child_ctx;
}

function get_each_context_1$1(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[9] = list[i].link;
	return child_ctx;
}

// (120:10) {#each item.links as {link}}
function create_each_block_1$1(ctx) {
	let a;
	let t_value = /*link*/ ctx[9].label + "";
	let t;
	let a_href_value;

	return {
		c() {
			a = element("a");
			t = text(t_value);
			this.h();
		},
		l(nodes) {
			a = claim_element(nodes, "A", { class: true, href: true });
			var a_nodes = children(a);
			t = claim_text(a_nodes, t_value);
			a_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "class", "link svelte-1xgioaj");
			attr(a, "href", a_href_value = /*link*/ ctx[9].url);
		},
		m(target, anchor) {
			insert_hydration(target, a, anchor);
			append_hydration(a, t);
		},
		p(ctx, dirty) {
			if (dirty & /*visible_items*/ 4 && t_value !== (t_value = /*link*/ ctx[9].label + "")) set_data(t, t_value);

			if (dirty & /*visible_items*/ 4 && a_href_value !== (a_href_value = /*link*/ ctx[9].url)) {
				attr(a, "href", a_href_value);
			}
		},
		d(detaching) {
			if (detaching) detach(a);
		}
	};
}

// (125:6) {#if item.thumbnail.url}
function create_if_block_1$2(ctx) {
	let img;
	let img_src_value;

	return {
		c() {
			img = element("img");
			this.h();
		},
		l(nodes) {
			img = claim_element(nodes, "IMG", { src: true, class: true });
			this.h();
		},
		h() {
			if (!src_url_equal(img.src, img_src_value = /*item*/ ctx[6].thumbnail.url)) attr(img, "src", img_src_value);
			attr(img, "class", "svelte-1xgioaj");
		},
		m(target, anchor) {
			insert_hydration(target, img, anchor);
		},
		p(ctx, dirty) {
			if (dirty & /*visible_items*/ 4 && !src_url_equal(img.src, img_src_value = /*item*/ ctx[6].thumbnail.url)) {
				attr(img, "src", img_src_value);
			}
		},
		d(detaching) {
			if (detaching) detach(img);
		}
	};
}

// (113:4) {#each visible_items as item (item.title)}
function create_each_block$2(key_1, ctx) {
	let li;
	let div2;
	let span;
	let t0_value = /*item*/ ctx[6].date + "";
	let t0;
	let t1;
	let h3;
	let t2_value = /*item*/ ctx[6].title + "";
	let t2;
	let t3;
	let div0;
	let raw_value = /*item*/ ctx[6].description.html + "";
	let t4;
	let div1;
	let t5;
	let t6;
	let li_intro;
	let each_value_1 = /*item*/ ctx[6].links;
	let each_blocks = [];

	for (let i = 0; i < each_value_1.length; i += 1) {
		each_blocks[i] = create_each_block_1$1(get_each_context_1$1(ctx, each_value_1, i));
	}

	let if_block = /*item*/ ctx[6].thumbnail.url && create_if_block_1$2(ctx);

	return {
		key: key_1,
		first: null,
		c() {
			li = element("li");
			div2 = element("div");
			span = element("span");
			t0 = text(t0_value);
			t1 = space();
			h3 = element("h3");
			t2 = text(t2_value);
			t3 = space();
			div0 = element("div");
			t4 = space();
			div1 = element("div");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			t5 = space();
			if (if_block) if_block.c();
			t6 = space();
			this.h();
		},
		l(nodes) {
			li = claim_element(nodes, "LI", { class: true });
			var li_nodes = children(li);
			div2 = claim_element(li_nodes, "DIV", {});
			var div2_nodes = children(div2);
			span = claim_element(div2_nodes, "SPAN", { class: true });
			var span_nodes = children(span);
			t0 = claim_text(span_nodes, t0_value);
			span_nodes.forEach(detach);
			t1 = claim_space(div2_nodes);
			h3 = claim_element(div2_nodes, "H3", { class: true });
			var h3_nodes = children(h3);
			t2 = claim_text(h3_nodes, t2_value);
			h3_nodes.forEach(detach);
			t3 = claim_space(div2_nodes);
			div0 = claim_element(div2_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			div0_nodes.forEach(detach);
			t4 = claim_space(div2_nodes);
			div1 = claim_element(div2_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(div1_nodes);
			}

			div1_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			t5 = claim_space(li_nodes);
			if (if_block) if_block.l(li_nodes);
			t6 = claim_space(li_nodes);
			li_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(span, "class", "date svelte-1xgioaj");
			attr(h3, "class", "title svelte-1xgioaj");
			attr(div0, "class", "description svelte-1xgioaj");
			attr(div1, "class", "links svelte-1xgioaj");
			attr(li, "class", "svelte-1xgioaj");
			this.first = li;
		},
		m(target, anchor) {
			insert_hydration(target, li, anchor);
			append_hydration(li, div2);
			append_hydration(div2, span);
			append_hydration(span, t0);
			append_hydration(div2, t1);
			append_hydration(div2, h3);
			append_hydration(h3, t2);
			append_hydration(div2, t3);
			append_hydration(div2, div0);
			div0.innerHTML = raw_value;
			append_hydration(div2, t4);
			append_hydration(div2, div1);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(div1, null);
				}
			}

			append_hydration(li, t5);
			if (if_block) if_block.m(li, null);
			append_hydration(li, t6);
		},
		p(new_ctx, dirty) {
			ctx = new_ctx;
			if (dirty & /*visible_items*/ 4 && t0_value !== (t0_value = /*item*/ ctx[6].date + "")) set_data(t0, t0_value);
			if (dirty & /*visible_items*/ 4 && t2_value !== (t2_value = /*item*/ ctx[6].title + "")) set_data(t2, t2_value);
			if (dirty & /*visible_items*/ 4 && raw_value !== (raw_value = /*item*/ ctx[6].description.html + "")) div0.innerHTML = raw_value;
			if (dirty & /*visible_items*/ 4) {
				each_value_1 = /*item*/ ctx[6].links;
				let i;

				for (i = 0; i < each_value_1.length; i += 1) {
					const child_ctx = get_each_context_1$1(ctx, each_value_1, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block_1$1(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(div1, null);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value_1.length;
			}

			if (/*item*/ ctx[6].thumbnail.url) {
				if (if_block) {
					if_block.p(ctx, dirty);
				} else {
					if_block = create_if_block_1$2(ctx);
					if_block.c();
					if_block.m(li, t6);
				}
			} else if (if_block) {
				if_block.d(1);
				if_block = null;
			}
		},
		i(local) {
			if (!li_intro) {
				add_render_callback(() => {
					li_intro = create_in_transition(li, slide, {});
					li_intro.start();
				});
			}
		},
		o: noop,
		d(detaching) {
			if (detaching) detach(li);
			destroy_each(each_blocks, detaching);
			if (if_block) if_block.d();
		}
	};
}

// (131:2) {#if !showing_all}
function create_if_block$3(ctx) {
	let button;
	let span;
	let t;
	let mounted;
	let dispose;

	return {
		c() {
			button = element("button");
			span = element("span");
			t = text("Show all");
			this.h();
		},
		l(nodes) {
			button = claim_element(nodes, "BUTTON", { class: true });
			var button_nodes = children(button);
			span = claim_element(button_nodes, "SPAN", { class: true });
			var span_nodes = children(span);
			t = claim_text(span_nodes, "Show all");
			span_nodes.forEach(detach);
			button_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(span, "class", "svelte-1xgioaj");
			attr(button, "class", "show-more svelte-1xgioaj");
		},
		m(target, anchor) {
			insert_hydration(target, button, anchor);
			append_hydration(button, span);
			append_hydration(span, t);

			if (!mounted) {
				dispose = listen(button, "click", /*click_handler*/ ctx[5]);
				mounted = true;
			}
		},
		p: noop,
		d(detaching) {
			if (detaching) detach(button);
			mounted = false;
			dispose();
		}
	};
}

function create_fragment$5(ctx) {
	let div1;
	let div0;
	let section;
	let h2;
	let t0;
	let t1;
	let ul;
	let each_blocks = [];
	let each_1_lookup = new Map();
	let t2;
	let each_value = /*visible_items*/ ctx[2];
	const get_key = ctx => /*item*/ ctx[6].title;

	for (let i = 0; i < each_value.length; i += 1) {
		let child_ctx = get_each_context$2(ctx, each_value, i);
		let key = get_key(child_ctx);
		each_1_lookup.set(key, each_blocks[i] = create_each_block$2(key, child_ctx));
	}

	let if_block = !/*showing_all*/ ctx[1] && create_if_block$3(ctx);

	return {
		c() {
			div1 = element("div");
			div0 = element("div");
			section = element("section");
			h2 = element("h2");
			t0 = text(/*heading*/ ctx[0]);
			t1 = space();
			ul = element("ul");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			t2 = space();
			if (if_block) if_block.c();
			this.h();
		},
		l(nodes) {
			div1 = claim_element(nodes, "DIV", { class: true, id: true });
			var div1_nodes = children(div1);
			div0 = claim_element(div1_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			section = claim_element(div0_nodes, "SECTION", { class: true });
			var section_nodes = children(section);
			h2 = claim_element(section_nodes, "H2", { class: true });
			var h2_nodes = children(h2);
			t0 = claim_text(h2_nodes, /*heading*/ ctx[0]);
			h2_nodes.forEach(detach);
			t1 = claim_space(section_nodes);
			ul = claim_element(section_nodes, "UL", { class: true });
			var ul_nodes = children(ul);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(ul_nodes);
			}

			ul_nodes.forEach(detach);
			t2 = claim_space(section_nodes);
			if (if_block) if_block.l(section_nodes);
			section_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h2, "class", "heading svelte-1xgioaj");
			attr(ul, "class", "items svelte-1xgioaj");
			attr(section, "class", "section-container svelte-1xgioaj");
			attr(div0, "class", "component");
			attr(div1, "class", "section");
			attr(div1, "id", "section-480e0dbd-e0a1-48b9-a3cf-19c0ac156811");
		},
		m(target, anchor) {
			insert_hydration(target, div1, anchor);
			append_hydration(div1, div0);
			append_hydration(div0, section);
			append_hydration(section, h2);
			append_hydration(h2, t0);
			append_hydration(section, t1);
			append_hydration(section, ul);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(ul, null);
				}
			}

			append_hydration(section, t2);
			if (if_block) if_block.m(section, null);
		},
		p(ctx, [dirty]) {
			if (dirty & /*heading*/ 1) set_data(t0, /*heading*/ ctx[0]);

			if (dirty & /*visible_items*/ 4) {
				each_value = /*visible_items*/ ctx[2];
				each_blocks = update_keyed_each(each_blocks, dirty, get_key, 1, ctx, each_value, each_1_lookup, ul, destroy_block, create_each_block$2, null, get_each_context$2);
			}

			if (!/*showing_all*/ ctx[1]) {
				if (if_block) {
					if_block.p(ctx, dirty);
				} else {
					if_block = create_if_block$3(ctx);
					if_block.c();
					if_block.m(section, null);
				}
			} else if (if_block) {
				if_block.d(1);
				if_block = null;
			}
		},
		i(local) {
			for (let i = 0; i < each_value.length; i += 1) {
				transition_in(each_blocks[i]);
			}
		},
		o: noop,
		d(detaching) {
			if (detaching) detach(div1);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].d();
			}

			if (if_block) if_block.d();
		}
	};
}

function instance$4($$self, $$props, $$invalidate) {
	let showing_all;
	let visible_items;
	let { heading } = $$props;
	let { items } = $$props;
	let { show_all } = $$props;
	const click_handler = () => $$invalidate(1, showing_all = true);

	$$self.$$set = $$props => {
		if ('heading' in $$props) $$invalidate(0, heading = $$props.heading);
		if ('items' in $$props) $$invalidate(3, items = $$props.items);
		if ('show_all' in $$props) $$invalidate(4, show_all = $$props.show_all);
	};

	$$self.$$.update = () => {
		if ($$self.$$.dirty & /*show_all*/ 16) {
			 $$invalidate(1, showing_all = show_all);
		}

		if ($$self.$$.dirty & /*items, showing_all*/ 10) {
			 $$invalidate(2, visible_items = items.slice(0, showing_all ? items.length : 3));
		}
	};

	return [heading, showing_all, visible_items, items, show_all, click_handler];
}

class Component$5 extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$4, create_fragment$5, safe_not_equal, { heading: 0, items: 3, show_all: 4 });
	}
}

/* generated by Svelte v3.58.0 */

function get_each_context$3(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[6] = list[i];
	return child_ctx;
}

function get_each_context_1$2(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[9] = list[i].link;
	return child_ctx;
}

// (120:10) {#each item.links as {link}}
function create_each_block_1$2(ctx) {
	let a;
	let t_value = /*link*/ ctx[9].label + "";
	let t;
	let a_href_value;

	return {
		c() {
			a = element("a");
			t = text(t_value);
			this.h();
		},
		l(nodes) {
			a = claim_element(nodes, "A", { class: true, href: true });
			var a_nodes = children(a);
			t = claim_text(a_nodes, t_value);
			a_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "class", "link svelte-1xgioaj");
			attr(a, "href", a_href_value = /*link*/ ctx[9].url);
		},
		m(target, anchor) {
			insert_hydration(target, a, anchor);
			append_hydration(a, t);
		},
		p(ctx, dirty) {
			if (dirty & /*visible_items*/ 4 && t_value !== (t_value = /*link*/ ctx[9].label + "")) set_data(t, t_value);

			if (dirty & /*visible_items*/ 4 && a_href_value !== (a_href_value = /*link*/ ctx[9].url)) {
				attr(a, "href", a_href_value);
			}
		},
		d(detaching) {
			if (detaching) detach(a);
		}
	};
}

// (125:6) {#if item.thumbnail.url}
function create_if_block_1$3(ctx) {
	let img;
	let img_src_value;

	return {
		c() {
			img = element("img");
			this.h();
		},
		l(nodes) {
			img = claim_element(nodes, "IMG", { src: true, class: true });
			this.h();
		},
		h() {
			if (!src_url_equal(img.src, img_src_value = /*item*/ ctx[6].thumbnail.url)) attr(img, "src", img_src_value);
			attr(img, "class", "svelte-1xgioaj");
		},
		m(target, anchor) {
			insert_hydration(target, img, anchor);
		},
		p(ctx, dirty) {
			if (dirty & /*visible_items*/ 4 && !src_url_equal(img.src, img_src_value = /*item*/ ctx[6].thumbnail.url)) {
				attr(img, "src", img_src_value);
			}
		},
		d(detaching) {
			if (detaching) detach(img);
		}
	};
}

// (113:4) {#each visible_items as item (item.title)}
function create_each_block$3(key_1, ctx) {
	let li;
	let div2;
	let span;
	let t0_value = /*item*/ ctx[6].date + "";
	let t0;
	let t1;
	let h3;
	let t2_value = /*item*/ ctx[6].title + "";
	let t2;
	let t3;
	let div0;
	let raw_value = /*item*/ ctx[6].description.html + "";
	let t4;
	let div1;
	let t5;
	let t6;
	let li_intro;
	let each_value_1 = /*item*/ ctx[6].links;
	let each_blocks = [];

	for (let i = 0; i < each_value_1.length; i += 1) {
		each_blocks[i] = create_each_block_1$2(get_each_context_1$2(ctx, each_value_1, i));
	}

	let if_block = /*item*/ ctx[6].thumbnail.url && create_if_block_1$3(ctx);

	return {
		key: key_1,
		first: null,
		c() {
			li = element("li");
			div2 = element("div");
			span = element("span");
			t0 = text(t0_value);
			t1 = space();
			h3 = element("h3");
			t2 = text(t2_value);
			t3 = space();
			div0 = element("div");
			t4 = space();
			div1 = element("div");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			t5 = space();
			if (if_block) if_block.c();
			t6 = space();
			this.h();
		},
		l(nodes) {
			li = claim_element(nodes, "LI", { class: true });
			var li_nodes = children(li);
			div2 = claim_element(li_nodes, "DIV", {});
			var div2_nodes = children(div2);
			span = claim_element(div2_nodes, "SPAN", { class: true });
			var span_nodes = children(span);
			t0 = claim_text(span_nodes, t0_value);
			span_nodes.forEach(detach);
			t1 = claim_space(div2_nodes);
			h3 = claim_element(div2_nodes, "H3", { class: true });
			var h3_nodes = children(h3);
			t2 = claim_text(h3_nodes, t2_value);
			h3_nodes.forEach(detach);
			t3 = claim_space(div2_nodes);
			div0 = claim_element(div2_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			div0_nodes.forEach(detach);
			t4 = claim_space(div2_nodes);
			div1 = claim_element(div2_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(div1_nodes);
			}

			div1_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			t5 = claim_space(li_nodes);
			if (if_block) if_block.l(li_nodes);
			t6 = claim_space(li_nodes);
			li_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(span, "class", "date svelte-1xgioaj");
			attr(h3, "class", "title svelte-1xgioaj");
			attr(div0, "class", "description svelte-1xgioaj");
			attr(div1, "class", "links svelte-1xgioaj");
			attr(li, "class", "svelte-1xgioaj");
			this.first = li;
		},
		m(target, anchor) {
			insert_hydration(target, li, anchor);
			append_hydration(li, div2);
			append_hydration(div2, span);
			append_hydration(span, t0);
			append_hydration(div2, t1);
			append_hydration(div2, h3);
			append_hydration(h3, t2);
			append_hydration(div2, t3);
			append_hydration(div2, div0);
			div0.innerHTML = raw_value;
			append_hydration(div2, t4);
			append_hydration(div2, div1);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(div1, null);
				}
			}

			append_hydration(li, t5);
			if (if_block) if_block.m(li, null);
			append_hydration(li, t6);
		},
		p(new_ctx, dirty) {
			ctx = new_ctx;
			if (dirty & /*visible_items*/ 4 && t0_value !== (t0_value = /*item*/ ctx[6].date + "")) set_data(t0, t0_value);
			if (dirty & /*visible_items*/ 4 && t2_value !== (t2_value = /*item*/ ctx[6].title + "")) set_data(t2, t2_value);
			if (dirty & /*visible_items*/ 4 && raw_value !== (raw_value = /*item*/ ctx[6].description.html + "")) div0.innerHTML = raw_value;
			if (dirty & /*visible_items*/ 4) {
				each_value_1 = /*item*/ ctx[6].links;
				let i;

				for (i = 0; i < each_value_1.length; i += 1) {
					const child_ctx = get_each_context_1$2(ctx, each_value_1, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block_1$2(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(div1, null);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value_1.length;
			}

			if (/*item*/ ctx[6].thumbnail.url) {
				if (if_block) {
					if_block.p(ctx, dirty);
				} else {
					if_block = create_if_block_1$3(ctx);
					if_block.c();
					if_block.m(li, t6);
				}
			} else if (if_block) {
				if_block.d(1);
				if_block = null;
			}
		},
		i(local) {
			if (!li_intro) {
				add_render_callback(() => {
					li_intro = create_in_transition(li, slide, {});
					li_intro.start();
				});
			}
		},
		o: noop,
		d(detaching) {
			if (detaching) detach(li);
			destroy_each(each_blocks, detaching);
			if (if_block) if_block.d();
		}
	};
}

// (131:2) {#if !showing_all}
function create_if_block$4(ctx) {
	let button;
	let span;
	let t;
	let mounted;
	let dispose;

	return {
		c() {
			button = element("button");
			span = element("span");
			t = text("Show all");
			this.h();
		},
		l(nodes) {
			button = claim_element(nodes, "BUTTON", { class: true });
			var button_nodes = children(button);
			span = claim_element(button_nodes, "SPAN", { class: true });
			var span_nodes = children(span);
			t = claim_text(span_nodes, "Show all");
			span_nodes.forEach(detach);
			button_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(span, "class", "svelte-1xgioaj");
			attr(button, "class", "show-more svelte-1xgioaj");
		},
		m(target, anchor) {
			insert_hydration(target, button, anchor);
			append_hydration(button, span);
			append_hydration(span, t);

			if (!mounted) {
				dispose = listen(button, "click", /*click_handler*/ ctx[5]);
				mounted = true;
			}
		},
		p: noop,
		d(detaching) {
			if (detaching) detach(button);
			mounted = false;
			dispose();
		}
	};
}

function create_fragment$6(ctx) {
	let div1;
	let div0;
	let section;
	let h2;
	let t0;
	let t1;
	let ul;
	let each_blocks = [];
	let each_1_lookup = new Map();
	let t2;
	let each_value = /*visible_items*/ ctx[2];
	const get_key = ctx => /*item*/ ctx[6].title;

	for (let i = 0; i < each_value.length; i += 1) {
		let child_ctx = get_each_context$3(ctx, each_value, i);
		let key = get_key(child_ctx);
		each_1_lookup.set(key, each_blocks[i] = create_each_block$3(key, child_ctx));
	}

	let if_block = !/*showing_all*/ ctx[1] && create_if_block$4(ctx);

	return {
		c() {
			div1 = element("div");
			div0 = element("div");
			section = element("section");
			h2 = element("h2");
			t0 = text(/*heading*/ ctx[0]);
			t1 = space();
			ul = element("ul");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			t2 = space();
			if (if_block) if_block.c();
			this.h();
		},
		l(nodes) {
			div1 = claim_element(nodes, "DIV", { class: true, id: true });
			var div1_nodes = children(div1);
			div0 = claim_element(div1_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			section = claim_element(div0_nodes, "SECTION", { class: true });
			var section_nodes = children(section);
			h2 = claim_element(section_nodes, "H2", { class: true });
			var h2_nodes = children(h2);
			t0 = claim_text(h2_nodes, /*heading*/ ctx[0]);
			h2_nodes.forEach(detach);
			t1 = claim_space(section_nodes);
			ul = claim_element(section_nodes, "UL", { class: true });
			var ul_nodes = children(ul);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(ul_nodes);
			}

			ul_nodes.forEach(detach);
			t2 = claim_space(section_nodes);
			if (if_block) if_block.l(section_nodes);
			section_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h2, "class", "heading svelte-1xgioaj");
			attr(ul, "class", "items svelte-1xgioaj");
			attr(section, "class", "section-container svelte-1xgioaj");
			attr(div0, "class", "component");
			attr(div1, "class", "section");
			attr(div1, "id", "section-6991af6d-d2f7-4617-a729-cae93576bbf1");
		},
		m(target, anchor) {
			insert_hydration(target, div1, anchor);
			append_hydration(div1, div0);
			append_hydration(div0, section);
			append_hydration(section, h2);
			append_hydration(h2, t0);
			append_hydration(section, t1);
			append_hydration(section, ul);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(ul, null);
				}
			}

			append_hydration(section, t2);
			if (if_block) if_block.m(section, null);
		},
		p(ctx, [dirty]) {
			if (dirty & /*heading*/ 1) set_data(t0, /*heading*/ ctx[0]);

			if (dirty & /*visible_items*/ 4) {
				each_value = /*visible_items*/ ctx[2];
				each_blocks = update_keyed_each(each_blocks, dirty, get_key, 1, ctx, each_value, each_1_lookup, ul, destroy_block, create_each_block$3, null, get_each_context$3);
			}

			if (!/*showing_all*/ ctx[1]) {
				if (if_block) {
					if_block.p(ctx, dirty);
				} else {
					if_block = create_if_block$4(ctx);
					if_block.c();
					if_block.m(section, null);
				}
			} else if (if_block) {
				if_block.d(1);
				if_block = null;
			}
		},
		i(local) {
			for (let i = 0; i < each_value.length; i += 1) {
				transition_in(each_blocks[i]);
			}
		},
		o: noop,
		d(detaching) {
			if (detaching) detach(div1);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].d();
			}

			if (if_block) if_block.d();
		}
	};
}

function instance$5($$self, $$props, $$invalidate) {
	let showing_all;
	let visible_items;
	let { heading } = $$props;
	let { items } = $$props;
	let { show_all } = $$props;
	const click_handler = () => $$invalidate(1, showing_all = true);

	$$self.$$set = $$props => {
		if ('heading' in $$props) $$invalidate(0, heading = $$props.heading);
		if ('items' in $$props) $$invalidate(3, items = $$props.items);
		if ('show_all' in $$props) $$invalidate(4, show_all = $$props.show_all);
	};

	$$self.$$.update = () => {
		if ($$self.$$.dirty & /*show_all*/ 16) {
			 $$invalidate(1, showing_all = show_all);
		}

		if ($$self.$$.dirty & /*items, showing_all*/ 10) {
			 $$invalidate(2, visible_items = items.slice(0, showing_all ? items.length : 3));
		}
	};

	return [heading, showing_all, visible_items, items, show_all, click_handler];
}

class Component$6 extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$5, create_fragment$6, safe_not_equal, { heading: 0, items: 3, show_all: 4 });
	}
}

/* generated by Svelte v3.58.0 */

function get_each_context$4(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[3] = list[i].item;
	child_ctx[4] = list[i].url;
	return child_ctx;
}

// (32:4) {#each items as {item, url}}
function create_each_block$4(ctx) {
	let li;
	let a;
	let t0_value = /*item*/ ctx[3] + "";
	let t0;
	let a_href_value;
	let t1;

	return {
		c() {
			li = element("li");
			a = element("a");
			t0 = text(t0_value);
			t1 = space();
			this.h();
		},
		l(nodes) {
			li = claim_element(nodes, "LI", { class: true });
			var li_nodes = children(li);
			a = claim_element(li_nodes, "A", { class: true, href: true });
			var a_nodes = children(a);
			t0 = claim_text(a_nodes, t0_value);
			a_nodes.forEach(detach);
			t1 = claim_space(li_nodes);
			li_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "class", "link");
			attr(a, "href", a_href_value = /*url*/ ctx[4]);
			attr(li, "class", "svelte-93bbb9");
		},
		m(target, anchor) {
			insert_hydration(target, li, anchor);
			append_hydration(li, a);
			append_hydration(a, t0);
			append_hydration(li, t1);
		},
		p(ctx, dirty) {
			if (dirty & /*items*/ 4 && t0_value !== (t0_value = /*item*/ ctx[3] + "")) set_data(t0, t0_value);

			if (dirty & /*items*/ 4 && a_href_value !== (a_href_value = /*url*/ ctx[4])) {
				attr(a, "href", a_href_value);
			}
		},
		d(detaching) {
			if (detaching) detach(li);
		}
	};
}

function create_fragment$7(ctx) {
	let div2;
	let div1;
	let section;
	let h2;
	let t0;
	let t1;
	let div0;
	let t2;
	let ul;
	let each_value = /*items*/ ctx[2];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block$4(get_each_context$4(ctx, each_value, i));
	}

	return {
		c() {
			div2 = element("div");
			div1 = element("div");
			section = element("section");
			h2 = element("h2");
			t0 = text(/*heading*/ ctx[0]);
			t1 = space();
			div0 = element("div");
			t2 = space();
			ul = element("ul");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			this.h();
		},
		l(nodes) {
			div2 = claim_element(nodes, "DIV", { class: true, id: true });
			var div2_nodes = children(div2);
			div1 = claim_element(div2_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			section = claim_element(div1_nodes, "SECTION", { class: true });
			var section_nodes = children(section);
			h2 = claim_element(section_nodes, "H2", { class: true });
			var h2_nodes = children(h2);
			t0 = claim_text(h2_nodes, /*heading*/ ctx[0]);
			h2_nodes.forEach(detach);
			t1 = claim_space(section_nodes);
			div0 = claim_element(section_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			div0_nodes.forEach(detach);
			t2 = claim_space(section_nodes);
			ul = claim_element(section_nodes, "UL", { class: true });
			var ul_nodes = children(ul);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(ul_nodes);
			}

			ul_nodes.forEach(detach);
			section_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h2, "class", "heading");
			attr(div0, "class", "description svelte-93bbb9");
			attr(ul, "class", "svelte-93bbb9");
			attr(section, "class", "section-container");
			attr(div1, "class", "component");
			attr(div2, "class", "section");
			attr(div2, "id", "section-6223f90b-1d33-4541-91f5-1b22624ef701");
		},
		m(target, anchor) {
			insert_hydration(target, div2, anchor);
			append_hydration(div2, div1);
			append_hydration(div1, section);
			append_hydration(section, h2);
			append_hydration(h2, t0);
			append_hydration(section, t1);
			append_hydration(section, div0);
			div0.innerHTML = /*description*/ ctx[1];
			append_hydration(section, t2);
			append_hydration(section, ul);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(ul, null);
				}
			}
		},
		p(ctx, [dirty]) {
			if (dirty & /*heading*/ 1) set_data(t0, /*heading*/ ctx[0]);
			if (dirty & /*description*/ 2) div0.innerHTML = /*description*/ ctx[1];
			if (dirty & /*items*/ 4) {
				each_value = /*items*/ ctx[2];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context$4(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block$4(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(ul, null);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value.length;
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div2);
			destroy_each(each_blocks, detaching);
		}
	};
}

function instance$6($$self, $$props, $$invalidate) {
	let { heading } = $$props;
	let { description } = $$props;
	let { items } = $$props;

	$$self.$$set = $$props => {
		if ('heading' in $$props) $$invalidate(0, heading = $$props.heading);
		if ('description' in $$props) $$invalidate(1, description = $$props.description);
		if ('items' in $$props) $$invalidate(2, items = $$props.items);
	};

	return [heading, description, items];
}

class Component$7 extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$6, create_fragment$7, safe_not_equal, { heading: 0, description: 1, items: 2 });
	}
}

/* generated by Svelte v3.58.0 */

function get_each_context$5(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[3] = list[i].link;
	child_ctx[4] = list[i].icon;
	return child_ctx;
}

// (107:6) {#each social_links as {link, icon}}
function create_each_block$5(ctx) {
	let li;
	let a;
	let icon;
	let a_href_value;
	let a_aria_label_value;
	let t;
	let current;
	icon = new Component$1({ props: { icon: /*icon*/ ctx[4] } });

	return {
		c() {
			li = element("li");
			a = element("a");
			create_component(icon.$$.fragment);
			t = space();
			this.h();
		},
		l(nodes) {
			li = claim_element(nodes, "LI", {});
			var li_nodes = children(li);

			a = claim_element(li_nodes, "A", {
				href: true,
				"aria-label": true,
				class: true
			});

			var a_nodes = children(a);
			claim_component(icon.$$.fragment, a_nodes);
			a_nodes.forEach(detach);
			t = claim_space(li_nodes);
			li_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "href", a_href_value = /*link*/ ctx[3].url);
			attr(a, "aria-label", a_aria_label_value = /*icon*/ ctx[4]);
			attr(a, "class", "svelte-1r1u4ef");
		},
		m(target, anchor) {
			insert_hydration(target, li, anchor);
			append_hydration(li, a);
			mount_component(icon, a, null);
			append_hydration(li, t);
			current = true;
		},
		p(ctx, dirty) {
			const icon_changes = {};
			if (dirty & /*social_links*/ 4) icon_changes.icon = /*icon*/ ctx[4];
			icon.$set(icon_changes);

			if (!current || dirty & /*social_links*/ 4 && a_href_value !== (a_href_value = /*link*/ ctx[3].url)) {
				attr(a, "href", a_href_value);
			}

			if (!current || dirty & /*social_links*/ 4 && a_aria_label_value !== (a_aria_label_value = /*icon*/ ctx[4])) {
				attr(a, "aria-label", a_aria_label_value);
			}
		},
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(li);
			destroy_component(icon);
		}
	};
}

function create_fragment$8(ctx) {
	let div3;
	let div2;
	let footer;
	let div0;
	let h2;
	let t0;
	let t1;
	let a0;
	let icon;
	let t2;
	let span0;
	let t3;
	let a0_href_value;
	let t4;
	let hr;
	let t5;
	let div1;
	let span1;
	let a1;
	let t6;
	let t7;
	let t8;
	let ul;
	let current;
	icon = new Component$1({ props: { icon: "mdi:envelope" } });
	let each_value = /*social_links*/ ctx[2];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block$5(get_each_context$5(ctx, each_value, i));
	}

	const out = i => transition_out(each_blocks[i], 1, 1, () => {
		each_blocks[i] = null;
	});

	return {
		c() {
			div3 = element("div");
			div2 = element("div");
			footer = element("footer");
			div0 = element("div");
			h2 = element("h2");
			t0 = text(/*heading*/ ctx[0]);
			t1 = space();
			a0 = element("a");
			create_component(icon.$$.fragment);
			t2 = space();
			span0 = element("span");
			t3 = text(/*email*/ ctx[1]);
			t4 = space();
			hr = element("hr");
			t5 = space();
			div1 = element("div");
			span1 = element("span");
			a1 = element("a");
			t6 = text("Primo");
			t7 = text(" Powered");
			t8 = space();
			ul = element("ul");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			this.h();
		},
		l(nodes) {
			div3 = claim_element(nodes, "DIV", { class: true, id: true });
			var div3_nodes = children(div3);
			div2 = claim_element(div3_nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			footer = claim_element(div2_nodes, "FOOTER", { class: true });
			var footer_nodes = children(footer);
			div0 = claim_element(footer_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			h2 = claim_element(div0_nodes, "H2", { class: true });
			var h2_nodes = children(h2);
			t0 = claim_text(h2_nodes, /*heading*/ ctx[0]);
			h2_nodes.forEach(detach);
			t1 = claim_space(div0_nodes);
			a0 = claim_element(div0_nodes, "A", { class: true, href: true });
			var a0_nodes = children(a0);
			claim_component(icon.$$.fragment, a0_nodes);
			t2 = claim_space(a0_nodes);
			span0 = claim_element(a0_nodes, "SPAN", { class: true });
			var span0_nodes = children(span0);
			t3 = claim_text(span0_nodes, /*email*/ ctx[1]);
			span0_nodes.forEach(detach);
			a0_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			t4 = claim_space(footer_nodes);
			hr = claim_element(footer_nodes, "HR", {});
			t5 = claim_space(footer_nodes);
			div1 = claim_element(footer_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			span1 = claim_element(div1_nodes, "SPAN", { class: true });
			var span1_nodes = children(span1);
			a1 = claim_element(span1_nodes, "A", { href: true, class: true });
			var a1_nodes = children(a1);
			t6 = claim_text(a1_nodes, "Primo");
			a1_nodes.forEach(detach);
			t7 = claim_text(span1_nodes, " Powered");
			span1_nodes.forEach(detach);
			t8 = claim_space(div1_nodes);
			ul = claim_element(div1_nodes, "UL", { class: true });
			var ul_nodes = children(ul);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(ul_nodes);
			}

			ul_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			footer_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			div3_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h2, "class", "heading svelte-1r1u4ef");
			attr(span0, "class", "svelte-1r1u4ef");
			attr(a0, "class", "email svelte-1r1u4ef");
			attr(a0, "href", a0_href_value = "mailto:" + /*email*/ ctx[1]);
			attr(div0, "class", "top svelte-1r1u4ef");
			attr(a1, "href", "https://primo.so");
			attr(a1, "class", "svelte-1r1u4ef");
			attr(span1, "class", "primo svelte-1r1u4ef");
			attr(ul, "class", "svelte-1r1u4ef");
			attr(div1, "class", "bottom svelte-1r1u4ef");
			attr(footer, "class", "section-container svelte-1r1u4ef");
			attr(div2, "class", "component");
			attr(div3, "class", "section");
			attr(div3, "id", "section-96b56eaa-28b0-4682-80ac-0e4fff9f901a");
		},
		m(target, anchor) {
			insert_hydration(target, div3, anchor);
			append_hydration(div3, div2);
			append_hydration(div2, footer);
			append_hydration(footer, div0);
			append_hydration(div0, h2);
			append_hydration(h2, t0);
			append_hydration(div0, t1);
			append_hydration(div0, a0);
			mount_component(icon, a0, null);
			append_hydration(a0, t2);
			append_hydration(a0, span0);
			append_hydration(span0, t3);
			append_hydration(footer, t4);
			append_hydration(footer, hr);
			append_hydration(footer, t5);
			append_hydration(footer, div1);
			append_hydration(div1, span1);
			append_hydration(span1, a1);
			append_hydration(a1, t6);
			append_hydration(span1, t7);
			append_hydration(div1, t8);
			append_hydration(div1, ul);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(ul, null);
				}
			}

			current = true;
		},
		p(ctx, [dirty]) {
			if (!current || dirty & /*heading*/ 1) set_data(t0, /*heading*/ ctx[0]);
			if (!current || dirty & /*email*/ 2) set_data(t3, /*email*/ ctx[1]);

			if (!current || dirty & /*email*/ 2 && a0_href_value !== (a0_href_value = "mailto:" + /*email*/ ctx[1])) {
				attr(a0, "href", a0_href_value);
			}

			if (dirty & /*social_links*/ 4) {
				each_value = /*social_links*/ ctx[2];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context$5(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
						transition_in(each_blocks[i], 1);
					} else {
						each_blocks[i] = create_each_block$5(child_ctx);
						each_blocks[i].c();
						transition_in(each_blocks[i], 1);
						each_blocks[i].m(ul, null);
					}
				}

				group_outros();

				for (i = each_value.length; i < each_blocks.length; i += 1) {
					out(i);
				}

				check_outros();
			}
		},
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);

			for (let i = 0; i < each_value.length; i += 1) {
				transition_in(each_blocks[i]);
			}

			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			each_blocks = each_blocks.filter(Boolean);

			for (let i = 0; i < each_blocks.length; i += 1) {
				transition_out(each_blocks[i]);
			}

			current = false;
		},
		d(detaching) {
			if (detaching) detach(div3);
			destroy_component(icon);
			destroy_each(each_blocks, detaching);
		}
	};
}

function instance$7($$self, $$props, $$invalidate) {
	let { heading } = $$props;
	let { email } = $$props;
	let { social_links } = $$props;

	$$self.$$set = $$props => {
		if ('heading' in $$props) $$invalidate(0, heading = $$props.heading);
		if ('email' in $$props) $$invalidate(1, email = $$props.email);
		if ('social_links' in $$props) $$invalidate(2, social_links = $$props.social_links);
	};

	return [heading, email, social_links];
}

class Component$8 extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$7, create_fragment$8, safe_not_equal, { heading: 0, email: 1, social_links: 2 });
	}
}

/* generated by Svelte v3.58.0 */

class Component$9 extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, null, null, safe_not_equal, {});
	}
}

/* generated by Svelte v3.58.0 */

function create_fragment$9(ctx) {
	let component_0;
	let t0;
	let component_1;
	let t1;
	let component_2;
	let t2;
	let component_3;
	let t3;
	let component_4;
	let t4;
	let component_5;
	let t5;
	let component_6;
	let t6;
	let component_7;
	let t7;
	let component_8;
	let current;
	component_0 = new Component({});

	component_1 = new Component$2({
			props: {
				logo: {
					"image": {
						"alt": "",
						"src": "https://picsum.photos/600/400?blur=10",
						"url": "https://picsum.photos/600/400?blur=10",
						"size": null
					},
					"title": "Ea reprehenderit ipsum"
				},
				site_nav: [
					{ "link": { "url": "/", "label": "Home" } },
					{
						"link": {
							"url": "https://primosites.vercel.app/resume",
							"label": "Resume"
						}
					},
					{ "link": { "url": "/", "label": "Talks" } }
				]
			}
		});

	component_2 = new Component$3({
			props: {
				portrait: {
					"alt": "",
					"src": "",
					"url": "",
					"size": null
				},
				name: "Mateo Morris",
				description: {
					"html": "<p>I’m a frontend developer/educator working on <a href=\"https://primo.so\">Primo</a> - a tool that makes web development more approachable by leveraging component-driven development &amp; <a href=\"https://svelte.dev\">Svelte</a>.</p>",
					"markdown": "I’m a frontend developer/educator working on [Primo](<https://primo.so>) \\- a tool that makes web development more approachable by leveraging component-driven development & [Svelte](<https://svelte.dev>).\n\n"
				},
				social_links: [
					{
						"icon": "mdi:twitter",
						"link": {
							"url": "https://twitter.com/_mateomorris",
							"label": "Twitter"
						}
					},
					{
						"icon": "mdi:github",
						"link": {
							"url": "https://github.com/mateomorris",
							"label": "Github"
						}
					}
				]
			}
		});

	component_3 = new Component$4({
			props: {
				content: {
					"html": "<h2>Intro</h2><p>I spent the first two years of my career poking around WordPress theme dashboards trying to get my website to do simple things, when what I really needed was to get to the code.</p><p>Unfortunately, things have only gone further since then with the growth of the <em>no-code </em>movement, which makes building websites easier in the short-term, but at the expense of cookie-cutter sites, expensive fees, and most importantly - the inability to access the platform.</p><p>HTML, CSS, and JavaScript are incredible tools for expression. They let anyone with a basic text editor and accessible education put anything on any screen in the world, without the permission of a middleman, and without the fear that it could be taken away or sold to the highest bidder.</p><p>Modern frontend development doesn't help much in this regard either. Countless students are churned through coding bootcamps every year, spending only a few weeks on these fundamental languages before learning the libraries and tools which seem to appeal to hiring managers. And as a result, many developers only learn how to do things with specialized tools without understanding the basics enough to know how to use them.</p><p>That's why tools which make empower web developers should not only build on those fundamentals, but make them as approachable as possible. <a target=\"_blank\" rel=\"noopener noreferrer nofollow\" class=\"link link link link link link link link link link link link\" href=\"https://kit.svelte.dev\"><strong>Svelte</strong></a> is a prime example of this - it literally builds on the fundamental languages of the web in that all valid HTML, CSS, and JavaScript is valid Svelte. It picks up where the web languages left off to enable component-driven development, reactivity, style encapsulation, and more, and its meta-framework <a target=\"_blank\" rel=\"noopener noreferrer nofollow\" class=\"link link link link link link link link link link link link\" href=\"https://kit.svelte.dev\"><strong>SvelteKit</strong></a> enables more people to build powerful full-stack web applications. Combined with feature-rich open-source backends like Supabase, modern developers are more capable than ever of building interactive, accessible, instantly and globally-available software.</p><p>But there's still a gap when it comes to content websites, the kinds of websites that most people need. This area is filled with a host of cookie-cutter monthly services which effectively rent out websites, or WordPress. WordPress is great, but only because Drupal's a pain. WordPress' developer experience, server-reliance, and security vulnerabilities are probably far outweighed by its benefits for most of the organizations using it, but for many of them (and many more who just can't use it) they're prohibitive.</p><p><a target=\"_blank\" rel=\"noopener noreferrer nofollow\" class=\"link link link link link link link link link link link link\" href=\"https://primo.so\"><strong>Primo</strong></a> is our attempt to build an intermediary tool - a <em>fully</em> approachable (any device, any technical background), enjoyable, and productive open-source tool for building and publishing common websites like blogs, landing pages, brochures, etc. Our hope is that it opens up the door for more people to start coding and publish their first live website within minutes without code, the command line, or documentation, creating a gradual learning curve towards modifying code and building full-stack applications.</p>",
					"markdown": "## Intro\n\nI spent the first two years of my career poking around WordPress theme dashboards trying to get my website to do simple things, when what I really needed was to get to the code.\n\nUnfortunately, things have only gone further since then with the growth of the *no-code *movement, which makes building websites easier in the short-term, but at the expense of cookie-cutter sites, expensive fees, and most importantly - the inability to access the platform.\n\nHTML, CSS, and JavaScript are incredible tools for expression. They let anyone with a basic text editor and accessible education put anything on any screen in the world, without the permission of a middleman, and without the fear that it could be taken away or sold to the highest bidder.\n\nModern frontend development doesn't help much in this regard either. Countless students are churned through coding bootcamps every year, spending only a few weeks on these fundamental languages before learning the libraries and tools which seem to appeal to hiring managers. And as a result, many developers only learn how to do things with specialized tools without understanding the basics enough to know how to use them.\n\nThat's why tools which make empower web developers should not only build on those fundamentals, but make them as approachable as possible. [**Svelte**](<https://kit.svelte.dev>) is a prime example of this - it literally builds on the fundamental languages of the web in that all valid HTML, CSS, and JavaScript is valid Svelte. It picks up where the web languages left off to enable component-driven development, reactivity, style encapsulation, and more, and its meta-framework [**SvelteKit**](<https://kit.svelte.dev>) enables more people to build powerful full-stack web applications. Combined with feature-rich open-source backends like Supabase, modern developers are more capable than ever of building interactive, accessible, instantly and globally-available software.\n\nBut there's still a gap when it comes to content websites, the kinds of websites that most people need. This area is filled with a host of cookie-cutter monthly services which effectively rent out websites, or WordPress. WordPress is great, but only because Drupal's a pain. WordPress' developer experience, server-reliance, and security vulnerabilities are probably far outweighed by its benefits for most of the organizations using it, but for many of them (and many more who just can't use it) they're prohibitive.\n\n[**Primo**](<https://primo.so>) is our attempt to build an intermediary tool - a *fully* approachable (any device, any technical background), enjoyable, and productive open-source tool for building and publishing common websites like blogs, landing pages, brochures, etc. Our hope is that it opens up the door for more people to start coding and publish their first live website within minutes without code, the command line, or documentation, creating a gradual learning curve towards modifying code and building full-stack applications.\n\n"
				}
			}
		});

	component_4 = new Component$5({
			props: {
				heading: "Previous Work",
				items: [
					{
						"date": "2018 - NewCity",
						"links": [
							{
								"link": {
									"url": "https://www.insidenewcity.com/work/oklahoma-state-university/",
									"label": "Case Study"
								}
							},
							{
								"link": {
									"url": "https://go.okstate.edu",
									"label": "Website"
								}
							}
						],
						"title": "Oklahoma State University",
						"thumbnail": {
							"alt": "Placeholder image",
							"src": "https://digitalassets.okstate.edu/transform/60014718-f3b9-43c8-b17c-f222d88f8b11/170820_class_of_2021_event_021-tif?io=transform:fill,width:975,height:650&quality=80",
							"url": "https://digitalassets.okstate.edu/transform/60014718-f3b9-43c8-b17c-f222d88f8b11/170820_class_of_2021_event_021-tif?io=transform:fill,width:975,height:650&quality=80",
							"size": null
						},
						"description": {
							"html": "<p>Built the frontend as components in Fractal that they put together into the main site and other departments' websites on subdomains. Seeing them take those base components and build out other sites was a large inspiration for thinking about how components work in Primo.</p>",
							"markdown": "Built the frontend as components in Fractal that they put together into the main site and other departments' websites on subdomains. Seeing them take those base components and build out other sites was a large inspiration for thinking about how components work in Primo.\n"
						}
					},
					{
						"date": "2017 - NewCity",
						"links": [
							{
								"link": {
									"url": "https://apps.apple.com/kg/app/blue-ridge-pkwy-travel-planner/id563085838",
									"label": "App Store"
								}
							}
						],
						"title": "Blue Ridge Parkway",
						"thumbnail": {
							"alt": "Placeholder image",
							"src": "https://www.virtualblueridge.com/wp-content/uploads/gallery-linn-cove-viaduct-in-spring.jpg",
							"url": "https://www.virtualblueridge.com/wp-content/uploads/gallery-linn-cove-viaduct-in-spring.jpg",
							"size": null
						},
						"description": {
							"html": "<p>Created official mobile app for iOS and Android using React Native &amp; a WordPress instance as a headless CMS.</p>",
							"markdown": "Created official mobile app for iOS and Android using React Native & a WordPress instance as a headless CMS.\n"
						}
					},
					{
						"date": "2017 - NewCity",
						"links": [
							{
								"link": {
									"url": "https://ed.unc.edu/",
									"label": "Website"
								}
							}
						],
						"title": "UNC: School of Education",
						"thumbnail": {
							"alt": "",
							"src": "https://www.unc.edu/wp-content/uploads/2021/07/020419_old_well_summer004-scaled-e1625573140177.jpg",
							"url": "https://www.unc.edu/wp-content/uploads/2021/07/020419_old_well_summer004-scaled-e1625573140177.jpg",
							"size": null
						},
						"description": {
							"html": "<p>Collaborated on frontend and handed off for integration with WordPress.</p>",
							"markdown": "Collaborated on frontend and handed off for integration with WordPress."
						}
					},
					{
						"date": "2017 - NewCity",
						"links": [
							{
								"link": {
									"url": "https://www.mcdaniel.edu/",
									"label": "Website"
								}
							}
						],
						"title": "McDaniel College",
						"thumbnail": {
							"alt": "McDaniel College",
							"src": "https://www.mcdaniel.edu/sites/default/files/styles/mobile_4x3/public/2019-09/General%20Campus_089.jpg?h=cda952af&itok=fa0bejpB",
							"url": "https://www.mcdaniel.edu/sites/default/files/styles/mobile_4x3/public/2019-09/General%20Campus_089.jpg?h=cda952af&itok=fa0bejpB",
							"size": null
						},
						"description": { "html": "", "markdown": "" }
					},
					{
						"date": "2017 - NewCity",
						"links": [
							{
								"link": {
									"url": "https://archdesign.utk.edu/",
									"label": "Website"
								}
							}
						],
						"title": "University of Tennessee: Architecture and Design",
						"thumbnail": {
							"alt": "",
							"src": "https://www.usnews.com/dims4/USNEWS/91e6fef/17177859217/resize/800x540%3E/quality/85/?url=https%3A%2F%2Fmedia.beam.usnews.com%2F78%2Faab209b61937fba4fb28a5fde2886e%2F_BP_5904.jpg",
							"url": "https://www.usnews.com/dims4/USNEWS/91e6fef/17177859217/resize/800x540%3E/quality/85/?url=https%3A%2F%2Fmedia.beam.usnews.com%2F78%2Faab209b61937fba4fb28a5fde2886e%2F_BP_5904.jpg",
							"size": null
						},
						"description": {
							"html": "<p>Collaborated on frontend to be handed off for integration with WordPress.</p>",
							"markdown": "Collaborated on frontend to be handed off for integration with WordPress."
						}
					},
					{
						"date": "2016 - NewCity",
						"links": [
							{
								"link": {
									"url": "https://www.med.emory.edu/",
									"label": "Website"
								}
							}
						],
						"title": "Emory University: School of Medicine",
						"thumbnail": {
							"alt": "",
							"src": "data:image/jpeg;base64,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",
							"url": "data:image/jpeg;base64,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",
							"size": null
						},
						"description": { "html": "", "markdown": "" }
					},
					{
						"date": "2016 - NewCity",
						"links": [
							{
								"link": {
									"url": "https://www.hollins.edu/175th-anniversary/",
									"label": "Website"
								}
							}
						],
						"title": "Hollins University's 175th Anniversary",
						"thumbnail": {
							"alt": "",
							"src": "https://www.hollins.edu/wp-content/uploads/2016/08/roosevelt_344x258_acf_cropped.jpg",
							"url": "https://www.hollins.edu/wp-content/uploads/2016/08/roosevelt_344x258_acf_cropped.jpg",
							"size": null
						},
						"description": {
							"html": "<p>Microsite for local university's anniversary, built and integrated into WordPress.</p>",
							"markdown": "Microsite for local university's anniversary, built and integrated into WordPress."
						}
					},
					{
						"date": "2016 - NewCity",
						"links": [],
						"title": "University of Kentucky",
						"thumbnail": {
							"alt": "",
							"src": "https://static.studyusa.com/school/cdn_4G_Va7R8tuQ-dD2j3804kKvqIXI50-G8.jpg?format=webp",
							"url": "https://static.studyusa.com/school/cdn_4G_Va7R8tuQ-dD2j3804kKvqIXI50-G8.jpg?format=webp",
							"size": null
						},
						"description": { "html": "", "markdown": "" }
					},
					{
						"date": "2016 - NewCity",
						"links": [],
						"title": "Pomona College: Benton Museum of Art",
						"thumbnail": {
							"alt": "",
							"src": "data:image/jpeg;base64,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",
							"url": "data:image/jpeg;base64,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",
							"size": null
						},
						"description": {
							"html": "<p>I built a custom page containing an interactive component that displayed posts from Instagram. I built it in React (this was before Svelte); it wasn't too bad, but getting my code updates onto the website was always painful.</p>",
							"markdown": "I built a custom page containing an interactive component that displayed posts from Instagram. I built it in React (this was before Svelte); it wasn't too bad, but getting my code updates onto the website was always painful."
						}
					},
					{
						"date": "2015 - NewCity",
						"links": [],
						"title": "Youngstown State University",
						"thumbnail": {
							"alt": "",
							"src": "https://www.jaggaer.com/app/uploads/2019/08/youngstown-ohio.jpg",
							"url": "https://www.jaggaer.com/app/uploads/2019/08/youngstown-ohio.jpg",
							"size": null
						},
						"description": {
							"html": "<p>One of the first projects I was a part of at NewCity. I shadowed a senior developer and learned how to build components stored in a Fractal component library using the Twig templating language &amp; SCSS.</p>",
							"markdown": "One of the first projects I was a part of at NewCity. I shadowed a senior developer and learned how to build components stored in a Fractal component library using the Twig templating language & SCSS."
						}
					}
				],
				show_all: ""
			}
		});

	component_5 = new Component$6({
			props: {
				heading: "Other things I've made",
				items: [
					{
						"date": "2019",
						"links": [],
						"title": "Primo Press",
						"thumbnail": {
							"alt": "",
							"src": "",
							"url": "",
							"size": null
						},
						"description": {
							"html": "<p>The precursor to Primo which started as a way to put up a curriculum page for my code bootcamp students at a custom domain without having to pay for hosting. I was close to monetizing it as a cheaper/simpler site builder, but seeing its potential as a dev tool encouraged me to expand its scope into Primo.</p>",
							"markdown": "The precursor to Primo which started as a way to put up a curriculum page for my code bootcamp students at a custom domain without having to pay for hosting. I was close to monetizing it as a cheaper/simpler site builder, but seeing its potential as a dev tool encouraged me to expand its scope into Primo."
						}
					},
					{
						"date": "2018",
						"links": [
							{
								"link": {
									"url": "https://boredorconfused.com",
									"label": "Website"
								}
							}
						],
						"title": "Bored or Confused",
						"thumbnail": {
							"alt": "",
							"src": "",
							"url": "",
							"size": null
						},
						"description": {
							"html": "<p>My first Svelte project - an app that allowed my students to quietly tell me if I had belabored too much on a topic (bored), or if I was going too fast (confused), as well as ask questions. It was working well, but then COVID hit.</p>",
							"markdown": "My first Svelte project - an app that allowed my students to quietly tell me if I had belabored too much on a topic (bored), or if I was going too fast (confused), as well as ask questions. It was working well, but then COVID hit."
						}
					},
					{
						"date": "2018",
						"links": [],
						"title": "Avopodo",
						"thumbnail": {
							"alt": "",
							"src": "",
							"url": "",
							"size": null
						},
						"description": {
							"html": "<p>The podcast app I always wanted to exist - with shows split up into subgroups (called \"stations\") that would shuffle all the latest episodes from each. Built in React Native, but abandoned when I started teaching (and frankly because React Native is pain and there were 2^<sup>42</sup> podcast apps by then).</p>",
							"markdown": "The podcast app I always wanted to exist - with shows split up into subgroups (called \"stations\") that would shuffle all the latest episodes from each. Built in React Native, but abandoned when I started teaching (and frankly because React Native is pain and there were 2^<sup>42</sup> podcast apps by then).\n\n"
						}
					},
					{
						"date": "2017",
						"links": [],
						"title": "Charity Miner",
						"thumbnail": {
							"alt": "",
							"src": "",
							"url": "",
							"size": null
						},
						"description": {
							"html": "<p>A Chrome extension that mined crypto with unused GPU. Unfortunately, the weirdness of doing it didn't outweigh the 0.1c/hour of value it generated.</p>",
							"markdown": "A Chrome extension that mined crypto with unused GPU. Unfortunately, the weirdness of doing it didn't outweigh the 0.1c/hour of value it generated."
						}
					}
				],
				show_all: ""
			}
		});

	component_6 = new Component$7({
			props: {
				heading: "Favorite tools",
				description: "",
				items: [
					{
						"url": "https://primo.so",
						"item": "Primo"
					},
					{
						"url": "https://kit.svelte.dev",
						"item": "SvelteKit"
					},
					{
						"url": "https://supabase.io",
						"item": "Supabase"
					},
					{
						"url": "https://developer.mozilla.org/en-US/docs/Web/CSS",
						"item": "CSS"
					},
					{
						"url": "https://cal.com",
						"item": "Cal.com"
					}
				]
			}
		});

	component_7 = new Component$8({
			props: {
				heading: "Get in touch",
				email: "mateo@primo.so",
				social_links: [
					{
						"icon": "mdi:twitter",
						"link": {
							"url": "https://twitter.com/_mateomorris",
							"label": "Twitter"
						}
					},
					{
						"icon": "mdi:github",
						"link": {
							"url": "https://github.com/mateomorris",
							"label": "Github"
						}
					}
				]
			}
		});

	component_8 = new Component$9({});

	return {
		c() {
			create_component(component_0.$$.fragment);
			t0 = space();
			create_component(component_1.$$.fragment);
			t1 = space();
			create_component(component_2.$$.fragment);
			t2 = space();
			create_component(component_3.$$.fragment);
			t3 = space();
			create_component(component_4.$$.fragment);
			t4 = space();
			create_component(component_5.$$.fragment);
			t5 = space();
			create_component(component_6.$$.fragment);
			t6 = space();
			create_component(component_7.$$.fragment);
			t7 = space();
			create_component(component_8.$$.fragment);
		},
		l(nodes) {
			claim_component(component_0.$$.fragment, nodes);
			t0 = claim_space(nodes);
			claim_component(component_1.$$.fragment, nodes);
			t1 = claim_space(nodes);
			claim_component(component_2.$$.fragment, nodes);
			t2 = claim_space(nodes);
			claim_component(component_3.$$.fragment, nodes);
			t3 = claim_space(nodes);
			claim_component(component_4.$$.fragment, nodes);
			t4 = claim_space(nodes);
			claim_component(component_5.$$.fragment, nodes);
			t5 = claim_space(nodes);
			claim_component(component_6.$$.fragment, nodes);
			t6 = claim_space(nodes);
			claim_component(component_7.$$.fragment, nodes);
			t7 = claim_space(nodes);
			claim_component(component_8.$$.fragment, nodes);
		},
		m(target, anchor) {
			mount_component(component_0, target, anchor);
			insert_hydration(target, t0, anchor);
			mount_component(component_1, target, anchor);
			insert_hydration(target, t1, anchor);
			mount_component(component_2, target, anchor);
			insert_hydration(target, t2, anchor);
			mount_component(component_3, target, anchor);
			insert_hydration(target, t3, anchor);
			mount_component(component_4, target, anchor);
			insert_hydration(target, t4, anchor);
			mount_component(component_5, target, anchor);
			insert_hydration(target, t5, anchor);
			mount_component(component_6, target, anchor);
			insert_hydration(target, t6, anchor);
			mount_component(component_7, target, anchor);
			insert_hydration(target, t7, anchor);
			mount_component(component_8, target, anchor);
			current = true;
		},
		p: noop,
		i(local) {
			if (current) return;
			transition_in(component_0.$$.fragment, local);
			transition_in(component_1.$$.fragment, local);
			transition_in(component_2.$$.fragment, local);
			transition_in(component_3.$$.fragment, local);
			transition_in(component_4.$$.fragment, local);
			transition_in(component_5.$$.fragment, local);
			transition_in(component_6.$$.fragment, local);
			transition_in(component_7.$$.fragment, local);
			transition_in(component_8.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(component_0.$$.fragment, local);
			transition_out(component_1.$$.fragment, local);
			transition_out(component_2.$$.fragment, local);
			transition_out(component_3.$$.fragment, local);
			transition_out(component_4.$$.fragment, local);
			transition_out(component_5.$$.fragment, local);
			transition_out(component_6.$$.fragment, local);
			transition_out(component_7.$$.fragment, local);
			transition_out(component_8.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			destroy_component(component_0, detaching);
			if (detaching) detach(t0);
			destroy_component(component_1, detaching);
			if (detaching) detach(t1);
			destroy_component(component_2, detaching);
			if (detaching) detach(t2);
			destroy_component(component_3, detaching);
			if (detaching) detach(t3);
			destroy_component(component_4, detaching);
			if (detaching) detach(t4);
			destroy_component(component_5, detaching);
			if (detaching) detach(t5);
			destroy_component(component_6, detaching);
			if (detaching) detach(t6);
			destroy_component(component_7, detaching);
			if (detaching) detach(t7);
			destroy_component(component_8, detaching);
		}
	};
}

class Component$a extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, null, create_fragment$9, safe_not_equal, {});
	}
}

export default Component$a;
