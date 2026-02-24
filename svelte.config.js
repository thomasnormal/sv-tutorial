import adapter from '@sveltejs/adapter-static';

const rawBase = process.env.VITE_BASE ?? '';
const base = rawBase.endsWith('/') ? rawBase.slice(0, -1) : rawBase;

export default {
  kit: {
    adapter: adapter({ fallback: '404.html' }),
    paths: { base }
  }
};
