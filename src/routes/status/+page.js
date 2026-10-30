import { lessonStatuses, statusSummary } from '$lib/generated-lesson-status.js';

export const prerender = true;

export function load() {
  return { lessonStatuses, statusSummary };
}
