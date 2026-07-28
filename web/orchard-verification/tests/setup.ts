import "@testing-library/jest-dom/vitest";

class ResizeObserverMock implements ResizeObserver {
  observe(): void {}
  unobserve(): void {}
  disconnect(): void {}
}

Object.defineProperty(globalThis, "ResizeObserver", {
  value: ResizeObserverMock,
  writable: true,
});

Object.defineProperty(globalThis, "matchMedia", {
  value: (query: string) => ({
    matches: false,
    media: query,
    onchange: null,
    addListener: () => undefined,
    removeListener: () => undefined,
    addEventListener: () => undefined,
    removeEventListener: () => undefined,
    dispatchEvent: () => false,
  }),
  writable: true,
});

Object.defineProperty(Element.prototype, "scrollIntoView", {
  value: () => undefined,
  configurable: true,
  writable: true,
});

Object.defineProperty(globalThis, "requestAnimationFrame", {
  value: (callback: FrameRequestCallback) =>
    globalThis.setTimeout(() => callback(performance.now()), 16),
  configurable: true,
  writable: true,
});

Object.defineProperty(globalThis, "cancelAnimationFrame", {
  value: (handle: number) => globalThis.clearTimeout(handle),
  configurable: true,
  writable: true,
});
