import { fileURLToPath, URL } from "node:url";
import react from "@vitejs/plugin-react";
import { defineConfig } from "vitest/config";

export default defineConfig({
  base: "./",
  plugins: [react()],
  server: {
    fs: {
      allow: [fileURLToPath(new URL("../..", import.meta.url))],
    },
  },
  build: {
    outDir: fileURLToPath(new URL("dist", import.meta.url)),
    emptyOutDir: true,
    rollupOptions: {
      input: {
        journey: fileURLToPath(new URL("index.html", import.meta.url)),
        map: fileURLToPath(new URL("proof-map.html", import.meta.url)),
        circuit: fileURLToPath(new URL("circuit.html", import.meta.url)),
        grid: fileURLToPath(new URL("circuit-grid.html", import.meta.url)),
      },
    },
  },
  test: {
    environment: "jsdom",
    setupFiles: "./tests/setup.ts",
    exclude: ["tests/e2e/**", "node_modules/**"],
    css: true,
  },
});
