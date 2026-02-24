import { redirect } from '@sveltejs/kit';
import { lessons } from '$lib/tutorial-data.js';
import { base } from '$app/paths';

// Not prerendered — served by the 404.html fallback on static hosts.
// Handles legacy ?lesson=N URLs by redirecting to the slug-based route at runtime.
export const prerender = false;

export function load({ url }) {
  const n = Number(url.searchParams.get('lesson'));
  const target = (Number.isFinite(n) && n >= 1 && n <= lessons.length) ? lessons[n - 1] : lessons[0];
  const [part, name] = target.slug.split('/');
  redirect(307, `${base}/lesson/${part}/${name}`);
}
