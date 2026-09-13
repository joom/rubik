// The browser owns the loop, so the extracted per-frame step is called back
// once per animation frame instead of being run to completion.
//
// This is the only place the web build differs from the native one. The cube,
// the panel, the camera and the solver are all the extracted Rocq program; the
// C++ here just hands it one frame at a time.

#include "rubik.h"

#include <emscripten/emscripten.h>

#include <cstdint>
#include <optional>
#include <utility>

namespace {

struct Session {
  config cfg;
  app state;
  bool finished = false;
};

void frame(void *arg) {
  auto *session = static_cast<Session *>(arg);
  if (session->finished) return;
  auto [stop, next] = step_frame(session->cfg, std::move(session->state));
  session->state = std::move(next);
  if (stop) {
    shutdown(session->cfg, session->state.a_job);
    session->finished = true;
    emscripten_cancel_main_loop();
  }
}

} // namespace

int main() {
  // raylib's web backend has no high-DPI support, so the canvas would be one
  // framebuffer pixel per CSS pixel and the browser would stretch it. Ask for
  // a framebuffer as dense as the display and let the layout scale to match.
  double ratio = emscripten_get_device_pixel_ratio();
  auto scale = static_cast<std::uint64_t>(ratio < 1.5 ? 1 : (ratio < 2.5 ? 2 : 3));
  // No screenshot path: the scripted self-test is for the command line.
  auto started = setup(scale, std::nullopt);
  static Session session{std::move(started.first), std::move(started.second)};
  // Paint once before yielding, so the first thing the page shows is the cube
  // rather than an empty canvas waiting on an animation frame.
  frame(&session);
  // A zero fps asks the browser for requestAnimationFrame, which matches the
  // display instead of fighting it.
  emscripten_set_main_loop_arg(frame, &session, 0, true);
  return 0;
}
