#pragma once

// Thin inline wrappers over raylib, one per effect declared in RaylibDefs.v.
// Nothing here knows about any particular application: the arguments are plain
// scalars and the only state is the frame's off-screen target stack.

#include "crane_real.h"

#include <raylib.h>
#include <rlgl.h>

#include <cstdint>
#include <cmath>
#include <string>
#include <utility>

// The opaque render-target handle Rocq sees.
using rl_texture = RenderTexture2D;
using rl_font = Font;

namespace rl_detail {

inline float f(Real v) { return static_cast<float>(v); }

inline Real real(float v) { return Real(static_cast<long double>(v)); }

inline unsigned char channel(std::uint64_t v) {
  return static_cast<unsigned char>(v > 255 ? 255 : v);
}

inline Color color(std::uint64_t r, std::uint64_t g, std::uint64_t b,
                   std::uint64_t a) {
  return Color{channel(r), channel(g), channel(b), channel(a)};
}

} // namespace rl_detail

// --- window lifetime and geometry ---

inline void rl_init_window(const std::string &title, std::uint64_t w,
                           std::uint64_t h) {
  SetConfigFlags(FLAG_MSAA_4X_HINT | FLAG_VSYNC_HINT);
  InitWindow(static_cast<int>(w), static_cast<int>(h), title.c_str());
}

inline void rl_close_window() {
  if (IsWindowReady()) CloseWindow();
}

inline bool rl_should_close() { return WindowShouldClose(); }

inline void rl_set_target_fps(std::uint64_t fps) {
  SetTargetFPS(static_cast<int>(fps));
}

inline std::pair<std::uint64_t, std::uint64_t> rl_screen_size() {
  return {static_cast<std::uint64_t>(GetScreenWidth()),
          static_cast<std::uint64_t>(GetScreenHeight())};
}

// --- frame boundaries ---

inline void rl_begin_drawing() { BeginDrawing(); }
inline void rl_end_drawing() { EndDrawing(); }

inline void rl_clear(std::uint64_t r, std::uint64_t g, std::uint64_t b,
                     std::uint64_t a) {
  ClearBackground(rl_detail::color(r, g, b, a));
}

// --- time and randomness ---

inline Real rl_time() { return Real(static_cast<long double>(GetTime())); }

inline std::uint64_t rl_random(std::uint64_t lo, std::uint64_t hi) {
  return static_cast<std::uint64_t>(
      GetRandomValue(static_cast<int>(lo), static_cast<int>(hi)));
}

// --- input ---

inline bool rl_key_pressed(std::uint64_t code) {
  return IsKeyPressed(static_cast<int>(code));
}

inline bool rl_key_down(std::uint64_t code) {
  return IsKeyDown(static_cast<int>(code));
}

inline bool rl_button_pressed(std::uint64_t code) {
  return IsMouseButtonPressed(static_cast<int>(code));
}

inline bool rl_button_down(std::uint64_t code) {
  return IsMouseButtonDown(static_cast<int>(code));
}

inline std::pair<Real, Real> rl_mouse() {
  const auto p = GetMousePosition();
  return {rl_detail::real(p.x), rl_detail::real(p.y)};
}

inline std::pair<Real, Real> rl_mouse_delta() {
  const auto p = GetMouseDelta();
  return {rl_detail::real(p.x), rl_detail::real(p.y)};
}

inline Real rl_wheel() { return rl_detail::real(GetMouseWheelMove()); }

// --- two-dimensional drawing ---

inline void rl_rectangle(Real x, Real y, Real w, Real h, Real roundness,
                         std::uint64_t r, std::uint64_t g, std::uint64_t b,
                         std::uint64_t a) {
  using rl_detail::f;
  const Rectangle box{f(x), f(y), f(w), f(h)};
  const Color fill = rl_detail::color(r, g, b, a);
  if (f(roundness) <= 0.0f) {
    DrawRectangleRec(box, fill);
  } else {
    DrawRectangleRounded(box, f(roundness), 8, fill);
  }
}

// --- fonts and text ---

inline rl_font rl_load_font(const std::string &path, std::uint64_t size) {
  const std::string full_path = std::string(GetApplicationDirectory()) + path;
  Font font = LoadFontEx(full_path.c_str(), static_cast<int>(size), nullptr, 0);
  if (IsFontValid(font)) SetTextureFilter(font.texture, TEXTURE_FILTER_BILINEAR);
  return font;
}

inline void rl_unload_font(rl_font font) {
  // LoadFontEx falls back to raylib's default atlas when a file is missing.
  if (IsFontValid(font) && font.texture.id != GetFontDefault().texture.id)
    UnloadFont(font);
}

inline void rl_text(rl_font font, const std::string &s, Real x, Real y,
                    std::uint64_t size, Real spacing,
                    std::uint64_t r, std::uint64_t g, std::uint64_t b,
                    std::uint64_t a) {
  using rl_detail::f;
  DrawTextEx(font, s.c_str(), {f(x), f(y)}, static_cast<float>(size), f(spacing),
             rl_detail::color(r, g, b, a));
}

inline std::uint64_t rl_text_width(rl_font font, const std::string &s,
                                   std::uint64_t size, Real spacing) {
  return static_cast<std::uint64_t>(std::ceil(
      MeasureTextEx(font, s.c_str(), static_cast<float>(size), rl_detail::f(spacing)).x));
}

// --- three-dimensional drawing ---

inline void rl_begin_3d(Real px, Real py, Real pz, Real tx, Real ty, Real tz,
                        Real ux, Real uy, Real uz, Real fovy) {
  using rl_detail::f;
  Camera3D camera{};
  camera.position = {f(px), f(py), f(pz)};
  camera.target = {f(tx), f(ty), f(tz)};
  camera.up = {f(ux), f(uy), f(uz)};
  camera.fovy = f(fovy);
  camera.projection = CAMERA_PERSPECTIVE;
  BeginMode3D(camera);
}

inline void rl_end_3d() { EndMode3D(); }

inline void rl_cube(Real x, Real y, Real z, Real w, Real h, Real d,
                    std::uint64_t r, std::uint64_t g, std::uint64_t b,
                    std::uint64_t a) {
  using rl_detail::f;
  DrawCubeV({f(x), f(y), f(z)}, {f(w), f(h), f(d)},
            rl_detail::color(r, g, b, a));
}

inline void rl_push() { rlPushMatrix(); }
inline void rl_pop() { rlPopMatrix(); }

inline void rl_rotate(Real degrees, Real x, Real y, Real z) {
  using rl_detail::f;
  rlRotatef(f(degrees), f(x), f(y), f(z));
}

// --- off-screen targets ---

inline rl_texture rl_load_target(std::uint64_t w, std::uint64_t h) {
  auto target = LoadRenderTexture(static_cast<int>(w), static_cast<int>(h));
  if (IsRenderTextureValid(target)) {
    SetTextureFilter(target.texture, TEXTURE_FILTER_BILINEAR);
  }
  return target;
}

inline void rl_unload_target(rl_texture t) {
  if (t.id) UnloadRenderTexture(t);
}

inline void rl_begin_target(rl_texture t) { BeginTextureMode(t); }
inline void rl_end_target() { EndTextureMode(); }

// raylib render targets are stored bottom-up, so the source height is negated.
inline void rl_draw_target(rl_texture t, Real x, Real y) {
  using rl_detail::f;
  const Rectangle source{0, 0, static_cast<float>(t.texture.width),
                         -static_cast<float>(t.texture.height)};
  DrawTextureRec(t.texture, source, {f(x), f(y)}, WHITE);
}

// --- files ---

inline void rl_screenshot(const std::string &path) {
  TakeScreenshot(path.c_str());
}

inline bool rl_file_exists(const std::string &path) {
  return FileExists(path.c_str());
}
