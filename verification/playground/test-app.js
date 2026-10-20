'use strict';

const assert = require('node:assert/strict');
const fs = require('node:fs');
const path = require('node:path');
const test = require('node:test');
const vm = require('node:vm');

const source = fs.readFileSync(path.join(__dirname, 'web/app.js'), 'utf8');
function section(first, next) {
  const start = source.indexOf(first);
  const end = source.indexOf(next, start);
  assert.ok(start >= 0 && end > start);
  return source.slice(start, end);
}

function harness() {
  const context = vm.createContext({
    current: { file: 'main.ml' }, value: 'let x = 1',
    ready: true, pending: null, requested: false, nextId: 0,
    editor: { getValue: () => context.value },
    performance: { now: () => 100 }, setTimeout: () => 1,
    clearTimeout() {}, worker: { postMessage() {} },
    checkButton: {}, stopButton: {}, erased: { hidden: true },
    lambda: { textContent: '' }, verdict: { dataset: {} },
    verdictDetail: {}, show() {}, renderDiagnostics() {}, markEditor() {},
    goalPanel: { clear() {}, show() {} },
  });
  vm.runInContext(section('function check()', 'stopButton.addEventListener(')
    + section('function finish(', 'function show('), context);
  return context;
}

test('a new check clears the previous erased program', () => {
  for (const result of [
    { result: { status: 2, output: 'Error: Unbound value missing',
      lambda: null } },
    { result: { status: 3, output: 'This program cannot be checked',
      lambda: null } },
    { error: 'Worker error' },
  ]) {
    const h = harness();
    h.check();
    h.finish({ result: { status: 0, output: '', queries: 0,
      lambda: 'let x = 1' } });
    assert.equal(h.erased.hidden, false);
    assert.equal(h.lambda.textContent, 'let x = 1');
    h.value = 'let x = missing';
    h.check();
    assert.equal(h.erased.hidden, true);
    assert.equal(h.lambda.textContent, '');
    h.finish(result.result
      ? { result: { queries: 0, ...result.result } } : result);
    assert.equal(h.erased.hidden, true);
    assert.equal(h.lambda.textContent, '');
  }
});

test('a changed program does not receive an old proof trace', () => {
  const h = harness();
  let displayed = false;
  h.goalPanel.show = () => { displayed = true; };
  h.check();
  h.value = 'let x = 2';
  h.finish({ result: { status: 0, output: '', queries: 1,
    lambda: null, proofQueries: [{ status: 'valid' }] } });
  assert.equal(displayed, false);
  assert.equal(h.verdict.dataset.state, 'stale');
});

test('proof traces are opt-in, bounded and reset between checks', async () => {
  const { createChecker } = require('./web/checker.js');
  let repeat = 1;
  const result = { status: 0, output: '', locations: [], lambda: null };
  const check = await createChecker({
    initZ3: async () => ({
      _Z3_mk_config: () => 1, _Z3_mk_context_rc: () => 1,
      _Z3_del_config() {}, _Z3_del_context() {},
      ccall: () => '(:version "4.16.0")',
    }),
    fetchBytes: async (name) => Buffer.from(name.endsWith('index.json')
      ? '{"files":[],"revision":"test"}' : ''),
    loadChecker: () => ({
      voxCheck() {
        for (let i = 0; i < repeat; i++) {
          globalThis.voxProofQuery?.({
            status: 'invalid', values: [{ name: 'n',
              value: '-4611686018427387904' }],
          });
        }
        return result;
      },
    }),
  });
  assert.equal(check('test.ml', '', false).proofQueries.length, 0);
  const captured = check('test.ml', '', false, true);
  assert.equal(captured.status, 0);
  assert.equal(captured.proofQueries.length, 1);
  assert.equal(captured.proofQueries[0].values[0].value,
    '-4611686018427387904');
  repeat = 102;
  const limited = check('test.ml', '', false, true);
  assert.equal(limited.proofQueries.length, 100);
  assert.equal(limited.proofQueriesTruncated, true);
  repeat = 1;
  assert.equal(check('test.ml', '', false, true).proofQueries.length, 1);
  assert.equal(globalThis.voxProofQuery, undefined);
});

test('guided lessons have sources and unique navigation entries', () => {
  const examples = JSON.parse(fs.readFileSync(
    path.join(__dirname, 'examples/index.json'), 'utf8'));
  assert.equal(examples.filter((example) => example.lesson).length, 6);
  assert.equal(new Set(examples.map((example) => example.file)).size,
    examples.length);
  for (const example of examples) {
    assert.ok(fs.existsSync(path.join(__dirname, 'examples', example.file)));
    if (example.lesson) {
      for (const field of ['title', 'body', 'challenge', 'detail']) {
        assert.ok(example.lesson[field]);
      }
    }
  }
});

test('goal inspection preserves exact values and treats names as text', () => {
  const goalSource = fs.readFileSync(
    path.join(__dirname, 'web/goals.js'), 'utf8');
  class Element {
    constructor(tag) { this.tag = tag; this.children = []; }
    append(...children) { this.children.push(...children); }
    replaceChildren(...children) { this.children = children; }
    setAttribute() {}
    addEventListener() {}
    set innerHTML(_) { throw new Error('Unexpected HTML rendering'); }
  }
  const context = vm.createContext({
    document: { createElement: (tag) => new Element(tag) },
  });
  vm.runInContext(goalSource, context);
  const root = new Element('section');
  const panel = context.createGoalPanel(root);
  panel.show([{
    label: 'result', status: 'invalid', assumptions: [],
    goal: '(n > 0)', reason: '', functions: [],
    values: [{ name: '<img src=x>', value: '1/3' }],
    modelAvailable: true, script: '(check-sat)',
  }], false);
  const contents = [];
  const visit = (node) => {
    if (node.textContent) contents.push(node.textContent);
    node.children.forEach(visit);
  };
  visit(root);
  assert.ok(contents.includes('<img src=x>'));
  assert.ok(contents.includes('1/3'));
  assert.equal(root.hidden, false);
  panel.clear();
  assert.equal(root.hidden, true);
  assert.equal(root.children.length, 0);
});
