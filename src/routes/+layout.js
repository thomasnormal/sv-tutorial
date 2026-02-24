import { lessons, parts } from '$lib/tutorial-data.js';

export const prerender = true;

export function load() {
  return { lessons, parts };
}
