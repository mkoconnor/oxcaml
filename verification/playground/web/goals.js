'use strict';

function createGoalPanel(root) {
  const statusNames = {
    valid: 'Proved', invalid: 'Countermodel', unknown: 'Unknown',
    timeout: 'Timed out', failure: 'Solver failed',
  };
  const element = (tag, text, className) => {
    const node = document.createElement(tag);
    if (text !== undefined) node.textContent = text;
    if (className) node.className = className;
    return node;
  };
  return {
    clear() {
      root.replaceChildren();
      root.hidden = true;
    },
    show(queries, truncated) {
      root.replaceChildren();
      root.hidden = !queries.length && !truncated;
      if (root.hidden) return;
      root.append(element('h2', 'Proof goals'));
      root.append(element('p',
        'These are the solver queries from this check, including retries and ' +
        'countermodel searches. The compiler verdict above is the result for ' +
        'the whole program. A countermodel is not a replayed execution.',
        'goal-note'));
      if (truncated) root.append(element('p',
        'Only the beginning of this check is shown: the display limit was ' +
        'reached. The compiler still checked the whole program.', 'goal-note'));
      const picker = element('select');
      picker.setAttribute('aria-label', 'Solver query');
      queries.forEach((query, index) => {
        const option = element('option',
          `${index + 1}. ${query.label} — ${statusNames[query.status]}`);
        option.value = String(index);
        picker.append(option);
      });
      const content = element('div');
      const render = (index) => {
        content.replaceChildren();
        const query = queries[index];
        if (!query) return;
        const assumptions = element('details');
        assumptions.append(element('summary',
          `Assumptions (${query.assumptions.length})`));
        for (const fact of query.assumptions) {
          assumptions.append(element('p', fact.label, 'goal-label'));
          assumptions.append(element('pre', fact.text));
        }
        content.append(assumptions, element('h3', 'Goal'),
          element('pre', query.goal, 'goal-conclusion'));
        if (query.reason) {
          content.append(element('p', query.reason, 'goal-note'));
        }
        if (query.status === 'invalid') {
          content.append(element('h3', 'Countermodel'));
          if (query.values.length) {
            const table = element('table');
            const header = element('tr');
            header.append(element('th', 'Name'), element('th', 'Value'));
            table.append(header);
            for (const value of query.values) {
              const row = element('tr');
              row.append(element('td', value.name),
                element('td', value.value));
              table.append(row);
            }
            content.append(table);
          } else {
            content.append(element('p', query.modelAvailable
              ? 'This query has no printable scalar values.'
              : 'Model values were not requested or could not be represented.',
            'goal-note'));
          }
        }
        if (query.functions.length) {
          content.append(element('p',
            `Opaque functions: ${query.functions.join(', ')}. ` +
            'A countermodel can indicate missing facts about these functions.',
          'goal-note'));
        }
        const details = element('details');
        details.append(element('summary', 'Exact SMT query'),
          element('pre', query.script));
        content.append(element('p',
          'Names are preserved from the compiler. “…” abbreviates nested ' +
          'expressions; the SMT query contains the complete formulas.',
        'goal-note'), details);
      };
      picker.addEventListener('change', () => render(Number(picker.value)));
      const firstFailure = queries.findIndex((q) => q.status !== 'valid');
      picker.value = String(firstFailure < 0 ? 0 : firstFailure);
      root.append(picker, content);
      render(Number(picker.value));
    },
  };
}

if (typeof module !== 'undefined') module.exports = { createGoalPanel };
