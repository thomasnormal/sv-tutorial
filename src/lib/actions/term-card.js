/**
 * Svelte action for lesson-body term hover cards.
 * Trigger: <dfn data-card="definition text">Term</dfn>
 * Uses event delegation so it works with {@ html} content.
 */
export function termCard(node, { onShow, onHide }) {
  let hideTimer = null;

  function handleMouseOver(e) {
    const dfn = e.target.closest('dfn[data-card]');
    if (!dfn) return;
    clearTimeout(hideTimer);
    onShow(dfn.dataset.card, dfn.getBoundingClientRect());
  }

  function handleMouseOut(e) {
    if (!e.target.closest('dfn[data-card]')) return;
    hideTimer = setTimeout(onHide, 200);
  }

  node.addEventListener('mouseover', handleMouseOver);
  node.addEventListener('mouseout', handleMouseOut);

  return {
    destroy() {
      clearTimeout(hideTimer);
      node.removeEventListener('mouseover', handleMouseOver);
      node.removeEventListener('mouseout', handleMouseOut);
    },
  };
}
