import { browser } from '$app/environment';
import { writable } from 'svelte/store';

const stored = browser ? localStorage.getItem('svt:done') : null;
let _initial = [];
if (stored) { try { _initial = JSON.parse(stored); } catch {} }
export const completedSlugs = writable(new Set(_initial));
if (browser) completedSlugs.subscribe(s => {
  try { localStorage.setItem('svt:done', JSON.stringify([...s])); } catch {}
});
