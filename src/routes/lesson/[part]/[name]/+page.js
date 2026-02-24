import { lessons } from '$lib/tutorial-data.js';
import { error } from '@sveltejs/kit';

export const prerender = true;

export function entries() {
  return lessons
    .filter(l => l?.slug)
    .map(l => { const [part, name] = l.slug.split('/'); return { part, name }; });
}

export function load({ params }) {
  const slug = `${params.part}/${params.name}`;
  const lesson = lessons.find(l => l.slug === slug);
  if (!lesson) error(404, 'Lesson not found');
  return { lesson };
}
