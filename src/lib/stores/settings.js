import { browser } from '$app/environment';
import { writable } from 'svelte/store';

function localStore(key, initial) {
  const stored = browser ? localStorage.getItem(key) : null;
  let value = initial;
  if (stored !== null) { try { value = JSON.parse(stored); } catch {} }
  const store = writable(value);
  if (browser) store.subscribe(v => { try { localStorage.setItem(key, JSON.stringify(v)); } catch {} });
  return store;
}

export const darkMode = localStore('svt:darkMode', false);
export const vimMode  = localStore('svt:vimMode',  false);
