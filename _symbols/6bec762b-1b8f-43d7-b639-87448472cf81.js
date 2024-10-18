// New Block - Updated October 18, 2024
function noop() { }
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
function is_empty(obj) {
    return Object.keys(obj).length === 0;
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
function element(name) {
    return document.createElement(name);
}
function text(data) {
    return document.createTextNode(data);
}
function space() {
    return text(' ');
}
function attr(node, attribute, value) {
    if (value == null)
        node.removeAttribute(attribute);
    else if (node.getAttribute(attribute) !== value)
        node.setAttribute(attribute, value);
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
const outroing = new Set();
function transition_in(block, local) {
    if (block && block.i) {
        outroing.delete(block);
        block.i(local);
    }
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

const exports$c = {}; const module$c = { exports: exports$c };

module$c.exports = ["#eee", "#d6e685", "#8cc665", "#44a340", "#1e6823"];



var __repl_0$4 = module$c.exports;

const __repl_lookup$4 = { 'github-calendar-legend': __repl_0$4 };

function require$4(id) {
	if (id in __repl_lookup$4) return __repl_lookup$4[id];
	throw new Error(`Cannot require modules dynamically (${id})`);
}

const exports$b = {}; const module$b = { exports: exports$b };

var colorLegend = require$4("github-calendar-legend");

/**
 * parseGitHubCalendarSvg
 * Parses the SVG input (as string).
 *
 * @name parseGitHubCalendarSvg
 * @function
 * @param {String} input The SVG code of the contributions calendar.
 * @return {Object} An object containing:
 *
 *  - `last_year` (Number): The total contributions in the last year.
 *  - `longest_streak` (Number): The longest streak.
 *  - `longest_streak_range` (Array): An array of two date objects representing the date range.
 *  - `current_streak` (Number): The current streak.
 *  - `current_streak_range` (Array): An array of two date objects representing the date range.
 *  - `days` (Array): An array of day objects:
 *       - `fill` (String): The hex color.
 *       - `date` (Date): The day date.
 *       - `count` (Number): The number of commits.
 *       - `level` (Number): A number between 0 and 4 (inclusive) representing the contribution level (more commits, higher value).
 *  - `weeks` (Array): The day objects grouped by weeks (arrays).
 *  - `last_contributed` (Date): The last contribution date.
 */
module$b.exports = function parseGitHubCalendarSvg(input) {

    var data = {
        last_year: 0,
        longest_streak: -1,
        longest_streak_range: [],
        current_streak: 0,
        current_streak_range: [],
        longest_break: -1,
        longest_break_range: [],
        current_break: 0,
        current_break_range: [],
        weeks: [],
        days: [],
        last_contributed: null
    },
        lastWeek = [],
        updateLongestStreak = function updateLongestStreak() {
        if (data.current_streak > data.longest_streak) {
            data.longest_streak = data.current_streak;
            data.longest_streak_range[0] = data.current_streak_range[0];
            data.longest_streak_range[1] = data.current_streak_range[1];
        }
    },
        updateLongestBreak = function updateLongestBreak() {
        if (data.current_break > data.longest_break) {
            data.longest_break = data.current_break;
            data.longest_break_range[0] = data.current_break_range[0];
            data.longest_break_range[1] = data.current_break_range[1];
        }
    };

    input.split("\n").slice(2).map(function (c) {
        return c.trim();
    }).forEach(function (c) {
        if (c.startsWith("<g transform")) {
            return lastWeek.length && data.weeks.push(lastWeek) && (lastWeek = []);
        }

        var level = c.match(/data-level="([0-9\-]+)"/i),
            date = c.match(/data-date="([0-9\-]+)"/),
            count = c.match(/(No|[0-9]+)( contribution)/);

        level = level && level[1];
        date = date && date[1];
        if (count) {
            if (count[1] === "No") {
                count[1] = 0;
            }
            count = +count[1];
        } else {
            count = 0;
        }

        if (!level) {
            return;
        }

        var fill = colorLegend[level];

        var obj = {
            fill: fill,
            date: new Date(date),
            count: count,
            level: level
        };

        if (data.current_streak === 0) {
            data.current_streak_range[0] = obj.date;
        }

        if (data.current_break === 0) {
            data.current_break_range[0] = obj.date;
        }

        if (obj.count) {
            ++data.current_streak;
            data.last_year += obj.count;
            data.last_contributed = obj.date;
            data.current_streak_range[1] = obj.date;

            updateLongestBreak();
            data.current_break = 0;
        } else {
            updateLongestStreak();
            data.current_streak = 0;

            ++data.current_break;
            data.current_break_range[1] = obj.date;
        }

        lastWeek.push(obj);
        data.days.push(obj);
    });

    updateLongestStreak();

    return data;
};



var __repl_0$3 = module$b.exports;

const exports$a = {}; const module$a = { exports: exports$a };

var _typeof = typeof Symbol === "function" && typeof Symbol.iterator === "symbol" ? function (obj) { return typeof obj; } : function (obj) { return obj && typeof Symbol === "function" && obj.constructor === Symbol && obj !== Symbol.prototype ? "symbol" : typeof obj; };

/**
 * iterateObject
 * Iterates an object. Note the object field order may differ.
 *
 * @name iterateObject
 * @function
 * @param {Object} obj The input object.
 * @param {Function} fn A function that will be called with the current value, field name and provided object.
 * @return {Function} The `iterateObject` function.
 */
function iterateObject(obj, fn) {
    var i = 0,
        keys = [];

    if (Array.isArray(obj)) {
        for (; i < obj.length; ++i) {
            if (fn(obj[i], i, obj) === false) {
                break;
            }
        }
    } else if ((typeof obj === "undefined" ? "undefined" : _typeof(obj)) === "object" && obj !== null) {
        keys = Object.keys(obj);
        for (; i < keys.length; ++i) {
            if (fn(obj[keys[i]], keys[i], obj) === false) {
                break;
            }
        }
    }
}

module$a.exports = iterateObject;



var __repl_0$2 = module$a.exports;

const exports$9 = {}; const module$9 = { exports: exports$9 };


/**
 * An Array.prototype.slice.call(arguments) alternative
 *
 * @param {Object} args something with a length
 * @param {Number} slice
 * @param {Number} sliceEnd
 * @api public
 */

module$9.exports = function (args, slice, sliceEnd) {
  var ret = [];
  var len = args.length;

  if (0 === len) return ret;

  var start = slice < 0
    ? Math.max(0, slice + len)
    : slice || 0;

  if (sliceEnd !== undefined) {
    len = sliceEnd < 0
      ? sliceEnd + len
      : sliceEnd;
  }

  while (len-- > start) {
    ret[len - start] = args[len];
  }

  return ret;
};





var __repl_1$2 = module$9.exports;

const __repl_lookup$3 = { 'iterate-object': __repl_0$2, 'sliced': __repl_1$2 };

function require$3(id) {
	if (id in __repl_lookup$3) return __repl_lookup$3[id];
	throw new Error(`Cannot require modules dynamically (${id})`);
}

const exports$8 = {}; const module$8 = { exports: exports$8 };

var iterateObj = require$3("iterate-object"),
    sliced = require$3("sliced");

/**
 * elly
 * Selects the DOM elements based on the provided selector. If there is no
 * commonjs/module environment, the `$` global variable will be created.
 *
 * @name elly
 * @function
 * @param {String|HTMLElement} input The element selector (e.g.
 * `'#my-id > .my-class'`), the element tag you want to create
 * (e.g. `'<ul>'`) or the HTML element (will be returned by the function).
 * @param {Object|HTMLElement} contextOrAttributes
 * @returns {HTMLElement} The HTMLElement that was provided or selected.
 */
function $$1(input, contextOrAttributes) {
    if (typeof input === "string") {
        if (input.charAt(0) === "<") {
            input = document.createElement(input.slice(1, -1));
            iterateObj(contextOrAttributes || {}, function (value, name) {

                switch (name) {
                    case "text":
                        input.textContent = value;
                        return;
                    case "html":
                        input.innerHTML = value;
                        return;
                }

                input.setAttribute(name, value);
            });
            return input;
        } else {
            contextOrAttributes = contextOrAttributes || document;
            return contextOrAttributes.querySelector(input);
        }
    }
    return input;
}
/**
 * elly.$$
 * Selects multiple elements. Note that if there is no commonjs/module environment, you will access this function using `$.$$`.
 *
 * @name elly.$$
 * @function
 * @param {String} selector The DOM query selector.
 * @param {HTMLElement} context The element context/container. Defaults to `document`.
 * @returns {Array} The array of elements.
 */
$$1.$$ = function (selector, context) {
    if (typeof selector === "string") {
        context = context || document;
        return sliced(context.querySelectorAll(selector));
    }
    return [selector];
};

module$8.exports = $$1;



var __repl_1$1 = module$8.exports;

const exports$7 = {}; const module$7 = { exports: exports$7 };

function gen(add) {
    return function _(d, count, what) {
        count = add * count;
        switch (what) {
            case "years":
            case "year":
                d.setFullYear(d.getFullYear() + count);
                break;
            case "months":
            case "month":
                d.setMonth(d.getMonth() + count);
                break;
            case "weeks":
            case "week":
                return _(d, count * 7, "days");
            case "days":
            case "day":
                d.setDate(d.getDate() + count);
                break;
            case "hours":
            case "hour":
                d.setHours(d.getHours() + count);
                break;
            case "minutes":
            case "minute":
                d.setMinutes(d.getMinutes() + count);
                break;
            case "seconds":
            case "second":
                d.setSeconds(d.getSeconds() + count);
                break;
            case "milliseconds":
            case "millisecond":
                d.setMilliseconds(d.getMilliseconds() + count);
                break;
            default:
                throw new Error("Invalid range: " + what);
        }
        return d;
    };
}

module$7.exports = {
    add: gen(1),
    subtract: gen(-1)
};



var __repl_2$1 = module$7.exports;

const exports$6 = {}; const module$6 = { exports: exports$6 };

/*!
 * months <https://github.com/datetime/months>
 *
 * Copyright (c) 2014-2017, Jon Schlinkert.
 * Released under the MIT License.
 */

// English Translation
module$6.exports = ['January', 'February', 'March', 'April', 'May', 'June', 'July', 'August', 'September', 'October', 'November', 'December'];
module$6.exports.abbr = ['Jan', 'Feb', 'Mar', 'Apr', 'May', 'Jun', 'Jul', 'Aug', 'Sep', 'Oct', 'Nov', 'Dec'];

// Italian Translation
module$6.exports.it = ['Gennaio', 'Febbraio', 'Marzo', 'Aprile', 'Maggio', 'Giugno', 'Luglio', 'Agosto', 'Settembre', 'Ottobre', 'Novembre', 'Dicembre'];
module$6.exports.abbr.it = ['Gen', 'Feb', 'Mar', 'Apr', 'Mag', 'Giu', 'Lug', 'Ago', 'Set', 'Ott', 'Nov', 'Dic'];

// German Translation
module$6.exports.de = [ 'Januar', 'Februar', 'März', 'April', 'Mai', 'Juni', 'Juli', 'August', 'September', 'Oktober', 'November', 'Dezember'];
module$6.exports.abbr.de = [ 'Jan', 'Feb', 'Mär', 'Apr', 'Mai', 'Jun', 'Jul', 'Aug', 'Sep', 'Okt', 'Nov', 'Dez' ];

// Greek Translation
module$6.exports.gr = ['Ιανουάριος', 'Φεβρουάριος', 'Μάρτιος', 'Απρίλιος', 'Μάιος', 'Ιούνιος', 'Ιούλιος', 'Αύγουστος', 'Σεπτέμβριος', 'Οκτώβριος', 'Νοέμβριος', 'Δεκέμβριος'];
module$6.exports.abbr.gr = ['Ιαν', 'Φεβρ', 'Μαρτ', 'Απρ', 'Μάιος', 'Ιούν', 'Ιούλ', 'Αυγ', 'Σεπτ', 'Οκτ', 'Νοεμ', 'Δεκ'];

// Dutch Translation
module$6.exports.nl = ['Januari', 'Februari', 'Maart', 'April', 'Mei', 'Juni', 'Juli', 'Augustus', 'September', 'Oktober', 'November', 'December'];
module$6.exports.abbr.nl = ['Jan', 'Feb', 'Maart', 'Apr', 'Mei', 'Juni', 'Juli', 'Aug', 'Sep', 'Okt', 'Nov', 'Dec'];

// Portuguese Translation
module$6.exports.pt = ['Janeiro', 'Fevereiro', 'Março', 'Abril', 'Maio', 'Junho', 'Julho', 'Agosto', 'Setembro', 'Outubro', 'Novembro', 'Dezembro'];
module$6.exports.abbr.pt = ['Jan', 'Fev', 'Mar', 'Abr', 'Mai', 'Jun', 'Jul', 'Ago', 'Set', 'Out', 'Nov', 'Dez'];




var __repl_0$1 = module$6.exports;

const exports$5 = {}; const module$5 = { exports: exports$5 };

/*!
 * days <https://github.com/jonschlinkert/days>
 *
 * Copyright (c) 2014-2017, Jon Schlinkert.
 * Released under the MIT License.
 */

// English
module$5.exports.en = ['Sunday', 'Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday', 'Saturday'];
module$5.exports.en.abbr = ['Sun', 'Mon', 'Tue', 'Wed', 'Thu', 'Fri', 'Sat'];
module$5.exports.en.short = ['Su', 'Mo', 'Tu', 'We', 'Th', 'Fr', 'Sa'];

// French translation
module$5.exports.fr = ['dimanche', 'lundi', 'mardi', 'mercredi', 'jeudi', 'vendredi', 'samedi'];
module$5.exports.fr.abbr = ['dim', 'lun', 'mar', 'mer', 'jeu', 'ven', 'sam'];
module$5.exports.fr.short = ['di', 'lu', 'ma', 'me', 'je', 've', 'sa'];

// Spanish translation
module$5.exports.es = ['domingo', 'lunes', 'martes', 'miercoles', 'jueves', 'viernes', 'sabado'];
module$5.exports.es.abbr = ['dom', 'lun', 'mar', 'mir', 'jue', 'vie', 'sab'];
module$5.exports.es.short = ['do', 'lu', 'ma', 'mi', 'ju', 'vi', 'sa'];

// Italian translation
module$5.exports.it = ['Domenica', 'Lunedi', 'Martedi', 'Mercoledi', 'Giovedi', 'Venerdi', 'Sabato'];
module$5.exports.it.abbr = ['Dom', 'Lun', 'Mar', 'Mer', 'Gio', 'Ven', 'Sab'];
module$5.exports.it.short = ['D', 'L', 'Ma', 'Me', 'G', 'V', 'S'];

// In order not to break compatibility
module$5.exports = ['Sunday', 'Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday', 'Saturday'];
module$5.exports.abbr = ['Sun', 'Mon', 'Tue', 'Wed', 'Thu', 'Fri', 'Sat'];
module$5.exports.short = ['Su', 'Mo', 'Tu', 'We', 'Th', 'Fr', 'Sa'];




var __repl_1 = module$5.exports;

const exports$4 = {}; const module$4 = { exports: exports$4 };

/**
 * fillo
 * Fill additional characters at the beginning of the string.
 *
 * @name fillo
 * @function
 * @param {String|Number} what The input snippet (number, string or anything that can be stringified).
 * @param {Number} size The width of the final string (default: `2`).
 * @param {String} ch The character to repeat (default: `"0"`).
 * @return {String} The input value with filled characters.
 */
module$4.exports = function fillo(what, size, ch) {
  size = size || 2;
  ch = ch || "0";
  what = what.toString();
  var howMany = size - what.length;
  return (howMany <= 0 ? "" : String(ch).repeat(howMany)) + what;
};



var __repl_2 = module$4.exports;

const exports$3 = {}; const module$3 = { exports: exports$3 };

/**
 * RegexEscape
 * Escapes a string for using it in a regular expression.
 *
 * @name RegexEscape
 * @function
 * @param {String} input The string that must be escaped.
 * @return {String} The escaped string.
 */
function RegexEscape(input) {
  return input.replace(/[\-\[\]\/\{\}\(\)\*\+\?\.\\\^\$\|]/g, "\\$&");
}

/**
 * proto
 * Adds the `RegexEscape` function to `RegExp` class.
 *
 * @name proto
 * @function
 * @return {Function} The `RegexEscape` function.
 */
RegexEscape.proto = function () {
  RegExp.escape = RegexEscape;
  return RegexEscape;
};

module$3.exports = RegexEscape;



var __repl_0 = module$3.exports;

const __repl_lookup$2 = { 'regex-escape': __repl_0 };

function require$2(id) {
	if (id in __repl_lookup$2) return __repl_lookup$2[id];
	throw new Error(`Cannot require modules dynamically (${id})`);
}

const exports$2 = {}; const module$2 = { exports: exports$2 };

var _createClass = function () { function defineProperties(target, props) { for (var i = 0; i < props.length; i++) { var descriptor = props[i]; descriptor.enumerable = descriptor.enumerable || false; descriptor.configurable = true; if ("value" in descriptor) descriptor.writable = true; Object.defineProperty(target, descriptor.key, descriptor); } } return function (Constructor, protoProps, staticProps) { if (protoProps) defineProperties(Constructor.prototype, protoProps); if (staticProps) defineProperties(Constructor, staticProps); return Constructor; }; }();

function _classCallCheck(instance, Constructor) { if (!(instance instanceof Constructor)) { throw new TypeError("Cannot call a class as a function"); } }

var regexEscape = require$2("regex-escape");

var ParseIt$1 = function () {
    /**
     * ParseIt
     * The `ParseIt` class. It can be used to use the same data object but with different formats/arguments.
     *
     * @name ParseIt
     * @function
     * @param {Object} obj An object containing the fields to replace.
     */
    function ParseIt(obj) {
        _classCallCheck(this, ParseIt);

        this.obj = obj || {};
        this.re = new RegExp("^(" + Object.keys(obj).map(regexEscape).join("|") + ")");
    }

    /**
     * run
     * Replaces the fields in the format string with data coming from the data object.
     *
     *
     * @name parseIt
     * @function
     * @param {String} format The format input.
     * @param {Array} args An array of arguments to be passed to the replace function (stored in the `obj` object).
     * @return {String} The result as string.
     */


    _createClass(ParseIt, [{
        key: "run",
        value: function run(format, args) {
            var result = "";
            args = args || [];
            do {
                var arr = format.match(this.re),
                    field = arr && arr[1],
                    c = field || format.charAt(0);

                if (field) {
                    var value = this.obj[field];
                    if (typeof value === "function") {
                        value = value.apply(this, args);
                    }
                    result += value;
                } else {
                    result += c;
                }
                format = format.substring(c.length);
            } while (format);
            return result;
        }
    }]);

    return ParseIt;
}();

/**
 * parseIt
 * A wrapper around the `ParseIt` class. The `ParseIt` constructor is accessible using `parseIt.Parser`.
 *
 * @name parseIt
 * @function
 * @param {String} format The format input.
 * @param {Object} obj An object containing the fields to replace.
 * @param {Array} args An array of arguments to be passed to the replace function (stored in the `obj` object).
 * @return {String} The result as string.
 */


function parseIt(format, obj, args) {
    return new ParseIt$1(obj).run(format, args);
}

parseIt.Parser = ParseIt$1;

module$2.exports = parseIt;



var __repl_3$1 = module$2.exports;

const __repl_lookup$1 = { 'months': __repl_0$1, 'days': __repl_1, 'fillo': __repl_2, 'parse-it': __repl_3$1 };

function require$1(id) {
	if (id in __repl_lookup$1) return __repl_lookup$1[id];
	throw new Error(`Cannot require modules dynamically (${id})`);
}

const exports$1 = {}; const module$1 = { exports: exports$1 };

var months = require$1("months"),
    days = require$1("days"),
    fillo = require$1("fillo"),
    ParseIt = require$1("parse-it").Parser;

var rules = {
    // Years
    /// 2015
    YYYY: function YYYY(i, utc) {
        if (utc) {
            return i.getUTCFullYear();
        }
        return i.getFullYear();
    }

    // 15
    ,
    YY: function YY(i, utc) {
        return rules.YYYY(i, utc) % 100;
    }

    // Months
    // January
    ,
    MMMM: function MMMM(i, utc) {
        if (utc) {
            return months[i.getUTCMonth()];
        }
        return months[i.getMonth()];
    }

    // Jan
    ,
    MMM: function MMM(i, utc) {
        if (utc) {
            return months.abbr[i.getUTCMonth()];
        }
        return months.abbr[i.getMonth()];
    }

    // 01
    ,
    MM: function MM(i, utc) {
        if (utc) {
            return fillo(i.getUTCMonth() + 1);
        }
        return fillo(i.getMonth() + 1);
    }

    // 1
    ,
    M: function M(i, utc) {
        if (utc) {
            return i.getUTCMonth() + 1;
        }
        return i.getMonth() + 1;
    }

    // Days
    // Sunday
    ,
    dddd: function dddd(i, utc) {
        return days[rules.d(i, utc)];
    }

    // Sun
    ,
    ddd: function ddd(i, utc) {
        return days.abbr[rules.d(i, utc)];
    }

    // Su
    ,
    dd: function dd(i, utc) {
        return days.short[rules.d(i, utc)];
    }

    // 0
    ,
    d: function d(i, utc) {
        if (utc) {
            return i.getUTCDay();
        }
        return i.getDay();
    }

    // Dates
    // 06  Day in month
    ,
    DD: function DD(i, utc) {
        return fillo(rules.D(i, utc));
    }

    // 6   Day in month
    ,
    D: function D(i, utc) {
        if (utc) {
            return i.getUTCDate();
        }
        return i.getDate();
    }

    // AM/PM
    // AM/PM
    ,
    A: function A(i, utc) {
        return rules.a(i, utc).toUpperCase();
    }

    // am/pm
    ,
    a: function a(i, utc) {
        return rules.H(i, utc) >= 12 ? "pm" : "am";
    }

    // Hours
    // 08 Hour
    ,
    hh: function hh(i, utc) {
        return fillo(rules.h(i, utc));
    }

    // 8 Hour
    ,
    h: function h(i, utc) {
        return rules.H(i, utc) % 12 || 12;
    }

    // (alias)
    ,
    HH: function HH(i, utc) {
        return fillo(rules.H(i, utc));
    }

    // (alias)
    ,
    H: function H(i, utc) {
        if (utc) {
            return i.getUTCHours();
        }
        return i.getHours();
    }

    // Minutes
    // 09 Minute
    ,
    mm: function mm(i, utc) {
        return fillo(rules.m(i, utc));
    }

    // 9  Minute
    ,
    m: function m(i, utc) {
        if (utc) {
            return i.getUTCMinutes();
        }
        return i.getMinutes();
    }

    // Seconds
    // 09 Seconds
    ,
    ss: function ss(i, utc) {
        return fillo(rules.s(i, utc));
    }

    // 9  Seconds
    ,
    s: function s(i, utc) {
        if (utc) {
            return i.getUTCSeconds();
        }
        return i.getSeconds();
    }

    // Fractional seconds
    // 0 1 ... 8 9
    ,
    S: function S(i, utc) {
        return Math.round(rules.s(i, utc) / 60 * 10);
    },
    SS: function SS(i, utc) {
        return fillo(rules.s(i, utc) / 60 * 100);
    },
    SSS: function SSS(i, utc) {
        return fillo(rules.s(i, utc) / 60 * 1000, 3);
    }

    // Timezones
    ,
    Z: function Z(i) {
        var offset = -i.getTimezoneOffset();
        return (offset >= 0 ? "+" : "-") + fillo(parseInt(offset / 60)) + ":" + fillo(offset % 60);
    },
    ZZ: function ZZ(i) {
        var offset = -i.getTimezoneOffset();
        return (offset >= 0 ? "+" : "-") + fillo(parseInt(offset / 60)) + fillo(offset % 60);
    }
};

var parser = new ParseIt(rules);

/**
 * formatoid
 * Formats the date into a given format.
 *
 * Usable format fields:
 *
 *  - **Years**
 *      - `YYYY` (e.g. `"2015"`)
 *      - `YY` (e.g. `"15"`)
 *  - **Months**
 *      - `MMMM` (e.g. `"January"`)
 *      - `MMM` (e.g. `"Jan"`)
 *      - `MM` (e.g. `"01"`)
 *      - `M` (e.g. `"1"`)
 *  - **Days**
 *      - `dddd` (e.g. `"Sunday"`)
 *      - `ddd` (e.g. `"Sun"`)
 *      - `dd` (e.g. `"Su"`)
 *      - `d` (e.g. `"Su"`)
 *  - **Dates**
 *      - `DD` (e.g. `"07"`)
 *      - `D` (e.g. `"7"`)
 *  - **AM/PM**
 *      - `A` (e.g. `"AM"`)
 *      - `a` (e.g. `"pm"`)
 *  - **Hours**
 *      - `hh` (e.g. `"07"`)–12 hour format
 *      - `h` (e.g. `"7"`)
 *      - `HH` (e.g. `"07"`)–24 hour format
 *      - `H` (e.g. `"7"`)
 *  - **Minutes**
 *      - `mm` (e.g. `"07"`)
 *      - `m` (e.g. `"7"`)
 *  - **Seconds**
 *      - `ss` (e.g. `"07"`)
 *      - `s` (e.g. `"7"`)
 *  - **Fractional seconds**
 *      - `S` (e.g. `0 1 2 3 ... 9`)
 *      - `SS` (e.g. `00 01 02 ... 98 99`)
 *      - `SS` (e.g. `000 001 002 ... 998 999`)
 *  - **Timezones**
 *      - `Z` (e.g. `-07:00 -06:00 ... +06:00 +07:00`)
 *      - `ZZ` (e.g. `-0700 -0600 ... +0600 +0700`)
 *
 * @name formatoid
 * @function
 * @param {Date} i The date object.
 * @param {String} f The date format.
 * @return {String} The formatted date (as string).
 */
module$1.exports = function formatoid(i, f) {
    return parser.run(f, [i, i._useUTC]);
};



var __repl_3 = module$1.exports;

const __repl_lookup = { 'github-calendar-parser': __repl_0$3, 'elly': __repl_1$1, 'add-subtract-date': __repl_2$1, 'formatoid': __repl_3 };

function require(id) {
	if (id in __repl_lookup) return __repl_lookup[id];
	throw new Error(`Cannot require modules dynamically (${id})`);
}

const exports = {}; const module = { exports };

var parse = require("github-calendar-parser"),
    $ = require("elly"),
    addSubtractDate = require("add-subtract-date"),
    formatoid = require("formatoid");

var DATE_FORMAT1 = "MMM D, YYYY",
    DATE_FORMAT2 = "MMMM D";

var MONTH_NAMES = ["Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec"];

function printDayCount(dayCount) {
    return dayCount + " " + (dayCount === 1 ? "day" : "days");
}

function addTooltips(container) {
    var tooltip = document.createElement("div");
    tooltip.classList.add("day-tooltip");
    container.appendChild(tooltip);

    // Add mouse event listener to show & hide tooltip
    var days = container.querySelectorAll(".js-calendar-graph-svg rect.ContributionCalendar-day");
    days.forEach(function (day) {
        day.addEventListener("mouseenter", function (e) {
            var contribCount = e.target.getAttribute("data-count");
            if (contribCount === "0") {
                contribCount = "No contributions";
            } else if (contribCount === "1") {
                contribCount = "1 contribution";
            } else {
                contribCount = contribCount + " contributions";
            }
            var date = new Date(e.target.getAttribute("data-date"));
            var dateText = MONTH_NAMES[date.getUTCMonth()] + " " + date.getUTCDate() + ", " + date.getUTCFullYear();
            tooltip.innerHTML = "<strong>" + contribCount + "</strong> on " + dateText;
            tooltip.classList.add("is-visible");
            var size = e.target.getBoundingClientRect(),
                leftPos = size.left + window.pageXOffset - tooltip.offsetWidth / 2 + size.width / 2,
                topPos = size.bottom + window.pageYOffset - tooltip.offsetHeight - 2 * size.height;
            tooltip.style.top = topPos + "px";
            tooltip.style.left = leftPos + "px";
        });
        day.addEventListener("mouseleave", function () {
            tooltip.classList.remove("is-visible");
        });
    });
}

/**
 * GitHubCalendar
 * Brings the contributions calendar from GitHub (provided username) into your page.
 *
 * @name GitHubCalendar
 * @function
 * @param {String|HTMLElement} container The calendar container (query selector or the element itself).
 * @param {String} username The GitHub username.
 * @param {Object} options An object containing the following fields:
 *
 *    - `summary_text` (String): The text that appears under the calendar (defaults to: `"Summary of
 *      pull requests, issues opened, and commits made by <username>"`).
 *    - `proxy` (Function): A function that receives as argument the username (string) and should return a promise resolving the HTML content of the contributions page.
 *      The default is using @Bloggify's APIs.
 *    - `global_stats` (Boolean): If `false`, the global stats (total, longest and current streaks) will not be calculated and displayed. By default this is enabled.
 *    - `responsive` (Boolean): If `true`, the graph is changed to scale with the container. Custom CSS should be applied to the element to scale it appropriately. By default this is disabled.
 *    - `tooltips` (Boolean): If `true`, tooltips will be shown when hovered over calendar days. By default this is disabled.
 *    - `cache` (Number) The cache time in seconds.
 *
 * @return {Promise} A promise returned by the `fetch()` call.
 */
module.exports = function GitHubCalendar(container, username, options) {

    container = $(container);

    options = options || {};
    options.summary_text = options.summary_text || "Summary of pull requests, issues opened, and commits made by <a href=\"https://github.com/" + username + "\" target=\"blank\">@" + username + "</a>";
    options.cache = (options.cache || 24 * 60 * 60) * 1000;

    if (options.global_stats === false) {
        container.style.minHeight = "175px";
    }

    var cacheKeys = {
        content: "gh_calendar_content." + username,
        expire_at: "gh_calendar_expire." + username

        // We need a proxy for CORS
    };options.proxy = options.proxy || function (username) {
        return fetch("https://api.bloggify.net/gh-calendar/?username=" + username).then(function (r) {
            return r.text();
        });
    };

    options.getCalendar = options.getCalendar || function (username) {
        if (options.cache && Date.now() < +localStorage.getItem(cacheKeys.expire_at)) {
            var content = localStorage.getItem(cacheKeys.content);
            if (content) {
                return Promise.resolve(content);
            }
        }

        return options.proxy(username).then(function (body) {
            if (options.cache) {
                localStorage.setItem(cacheKeys.content, body);
                localStorage.setItem(cacheKeys.expire_at, Date.now() + options.cache);
            }
            return body;
        });
    };

    var fetchCalendar = function fetchCalendar() {
        return options.getCalendar(username).then(function (body) {
            var div = document.createElement("div");
            div.innerHTML = body;
            var cal = div.querySelector(".js-yearly-contributions");
            $(".position-relative h2", cal).remove();
            //cal.querySelector(".float-left.text-gray").innerHTML = options.summary_text

            // Remove 3d visualiser div
            var _iteratorNormalCompletion = true;
            var _didIteratorError = false;
            var _iteratorError = undefined;

            try {
                for (var _iterator = div.querySelectorAll("a")[Symbol.iterator](), _step; !(_iteratorNormalCompletion = (_step = _iterator.next()).done); _iteratorNormalCompletion = true) {
                    var a = _step.value;

                    if (a.textContent.includes("View your contributions in 3D, VR and IRL!")) {
                        a.parentElement.remove();
                    }
                }

                // If 'include-fragment' with spinner img loads instead of the svg, fetchCalendar again
            } catch (err) {
                _didIteratorError = true;
                _iteratorError = err;
            } finally {
                try {
                    if (!_iteratorNormalCompletion && _iterator.return) {
                        _iterator.return();
                    }
                } finally {
                    if (_didIteratorError) {
                        throw _iteratorError;
                    }
                }
            }

            if (cal.querySelector("include-fragment")) {
                setTimeout(fetchCalendar, 500);
            } else {
                // If options includes responsive, SVG element has to be manipulated to be made responsive
                if (options.responsive === true) {
                    var svg = cal.querySelector("table.js-calendar-graph-table");
                    // Get the width/height properties and use them to create the viewBox
                    var width = svg.getAttribute("width");
                    var height = svg.getAttribute("height");
                    // Remove height property entirely
                    svg.removeAttribute("height");
                    // Width property should be set to 100% to fill entire container
                    svg.setAttribute("width", "100%");
                    // Add a viewBox property based on the former width/height
                    svg.setAttribute("viewBox", "0 0 " + width + " " + height);
                }

                if (options.global_stats !== false) {
                    var parsed = parse(cal.innerHTML),
                        currentStreakInfo = parsed.current_streak ? formatoid(parsed.current_streak_range[0], DATE_FORMAT2) + " &ndash; " + formatoid(parsed.current_streak_range[1], DATE_FORMAT2) : parsed.last_contributed ? "Last contributed in " + formatoid(parsed.last_contributed, DATE_FORMAT2) + "." : "Rock - Hard Place",
                        longestStreakInfo = parsed.longest_streak ? formatoid(parsed.longest_streak_range[0], DATE_FORMAT2) + " &ndash; " + formatoid(parsed.longest_streak_range[1], DATE_FORMAT2) : parsed.last_contributed ? "Last contributed in " + formatoid(parsed.last_contributed, DATE_FORMAT2) + "." : "Rock - Hard Place",
                        firstCol = $("<div>", {
                        "class": "contrib-column contrib-column-first table-column",
                        html: "<span class=\"text-muted\">Contributions in the last year</span>\n                               <span class=\"contrib-number\">" + parsed.last_year + " total</span>\n                               <span class=\"text-muted\">" + formatoid(addSubtractDate.add(addSubtractDate.subtract(new Date(), 1, "year"), 1, "day"), DATE_FORMAT1) + " &ndash; " + formatoid(new Date(), DATE_FORMAT1) + "</span>"
                    }),
                        secondCol = $("<div>", {
                        "class": "contrib-column table-column",
                        html: "<span class=\"text-muted\">Longest streak</span>\n                               <span class=\"contrib-number\">" + printDayCount(parsed.longest_streak) + "</span>\n                               <span class=\"text-muted\">" + longestStreakInfo + "</span>"
                    }),
                        thirdCol = $("<div>", {
                        "class": "contrib-column table-column",
                        html: "<span class=\"text-muted\">Current streak</span>\n                               <span class=\"contrib-number\">" + printDayCount(parsed.current_streak) + "</span>\n                               <span class=\"text-muted\">" + currentStreakInfo + "</span>"
                    });

                    cal.appendChild(firstCol);
                    cal.appendChild(secondCol);
                    cal.appendChild(thirdCol);
                }

                container.innerHTML = cal.innerHTML;

                // If options includes tooltips, add tooltips listeners to SVG
                if (options.tooltips === true) {
                    addTooltips(container);
                }
            }
        }).catch(function (e) {
            return console.error(e);
        });
    };

    return fetchCalendar();
};



var GithubCalendar = module.exports;

/* generated by Svelte v3.59.1 */

function create_fragment(ctx) {
	let link;
	let t0;
	let div1;
	let div0;
	let t1;

	return {
		c() {
			link = element("link");
			t0 = space();
			div1 = element("div");
			div0 = element("div");
			t1 = text("Loading the data just for you.");
			this.h();
		},
		l(nodes) {
			link = claim_element(nodes, "LINK", { rel: true, href: true });
			t0 = claim_space(nodes);
			div1 = claim_element(nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			div0 = claim_element(div1_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			t1 = claim_text(div0_nodes, "Loading the data just for you.");
			div0_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(link, "rel", "stylesheet");
			attr(link, "href", "https://unpkg.com/github-calendar@latest/dist/github-calendar-responsive.css");
			attr(div0, "class", "calendar");
			attr(div1, "class", "section-container");
		},
		m(target, anchor) {
			insert_hydration(target, link, anchor);
			insert_hydration(target, t0, anchor);
			insert_hydration(target, div1, anchor);
			append_hydration(div1, div0);
			append_hydration(div0, t1);
		},
		p: noop,
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(link);
			if (detaching) detach(t0);
			if (detaching) detach(div1);
		}
	};
}

function instance($$self, $$props, $$invalidate) {
	let { props } = $$props;

	onMount(() => {
		console.log({ GithubCalendar });
		GithubCalendar(".calendar", "mateomorris", { responsive: true });
	});

	$$self.$$set = $$props => {
		if ('props' in $$props) $$invalidate(0, props = $$props.props);
	};

	return [props];
}

class Component extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance, create_fragment, safe_not_equal, { props: 0 });
	}
}

export { Component as default };
