(** * Generic raylib bindings: shared definitions

    Handle types, geometry, colors, input names, and the raylib effect functor,
    all independent of the extraction flavor. [Raylib.v] re-exports this module
    and adds the C++ extraction mappings. Nothing here mentions a cube: any
    application can build on these. *)

From Corelib Require Import PrimString.
From Stdlib Require Import List Reals.
From Crane Require Import Mapping.Std Monads.ITree.
From Crane Require Extraction.
Import ListNotations.

(** * Handles *)

(** An opaque off-screen render target owned by the graphics library. *)
Axiom rl_texture : Type.

(** * Geometry and color *)

(** A point or a direction in raylib's right-handed world space. *)
Record rl_vec3 : Type := Vec3 { v3x : R; v3y : R; v3z : R }.

(** Componentwise sum of two vectors. *)
Definition v3_add (a b : rl_vec3) : rl_vec3 :=
  Vec3 (v3x a + v3x b)%R (v3y a + v3y b)%R (v3z a + v3z b)%R.

(** A vector stretched by a factor. *)
Definition v3_scale (s : R) (a : rl_vec3) : rl_vec3 :=
  Vec3 (s * v3x a)%R (s * v3y a)%R (s * v3z a)%R.

(** The dot product of two vectors. *)
Definition v3_dot (a b : rl_vec3) : R :=
  (v3x a * v3x b + v3y a * v3y b + v3z a * v3z b)%R.

(** The cross product, right-handed. *)
Definition v3_cross (a b : rl_vec3) : rl_vec3 :=
  Vec3 (v3y a * v3z b - v3z a * v3y b)%R
       (v3z a * v3x b - v3x a * v3z b)%R
       (v3x a * v3y b - v3y a * v3x b)%R.

(** The length of a vector. *)
Definition v3_length (a : rl_vec3) : R := sqrt (v3_dot a a).

(** A vector scaled to unit length. The zero vector is left alone. *)
Definition v3_unit (a : rl_vec3) : rl_vec3 :=
  let n := v3_length a in
  if Rle_dec n 0 then a else v3_scale (1 / n)%R a.

(** A screen-space rectangle given by its top-left corner and its extent. *)
Record rl_rect : Type := Rect { rx : R; ry : R; rw : R; rh : R }.

(** A straight RGBA color, one byte per channel. *)
Record rl_color : Type := RGBA { cr : nat; cg : nat; cb : nat; ca : nat }.

(** An opaque color, the common case. *)
Definition rgb (r g b : nat) : rl_color := RGBA r g b 255.

(** Scale a color's alpha by a fraction of full opacity. *)
Definition fade (c : rl_color) (num den : nat) : rl_color :=
  RGBA (cr c) (cg c) (cb c) (Nat.div (Nat.mul (ca c) num) den).

(** A perspective camera looking at a target from a position. *)
Record rl_camera : Type :=
  Camera { cam_at : rl_vec3; cam_to : rl_vec3; cam_up : rl_vec3; cam_fovy : R }.

(** Whether a screen point lies inside a rectangle. *)
Definition in_rect (x y : R) (r : rl_rect) : bool :=
  if Rle_dec (rx r) x then
    if Rlt_dec x (rx r + rw r)%R then
      if Rle_dec (ry r) y then
        if Rlt_dec y (ry r + rh r)%R then true else false
      else false
    else false
  else false.

(** * Input names *)

(** Keyboard keys, named so that applications never spell out raylib numbers. *)
Inductive rl_key : Type :=
| KeyA | KeyB | KeyC | KeyD | KeyE | KeyF
| KeyG | KeyH | KeyI | KeyJ | KeyK | KeyL
| KeyM | KeyN | KeyO | KeyP | KeyQ | KeyR
| KeyS | KeyT | KeyU | KeyV | KeyW | KeyX
| KeyY | KeyZ | KeyNum0 | KeyNum1 | KeyNum2 | KeyNum3
| KeyNum4 | KeyNum5 | KeyNum6 | KeyNum7 | KeyNum8 | KeyNum9
| KeySpace | KeyApostrophe | KeyComma | KeyMinus | KeyPeriod | KeySlash
| KeySemicolon | KeyEqual | KeyLeftBracket | KeyBackslash | KeyRightBracket | KeyGrave
| KeyEscape | KeyEnter | KeyTab | KeyBackspace | KeyInsert | KeyDelete
| KeyRight | KeyLeft | KeyDown | KeyUp | KeyPageUp | KeyPageDown
| KeyHome | KeyEnd | KeyCapsLock | KeyScrollLock | KeyNumLock | KeyPrintScreen
| KeyPause | KeyF1 | KeyF2 | KeyF3 | KeyF4 | KeyF5
| KeyF6 | KeyF7 | KeyF8 | KeyF9 | KeyF10 | KeyF11
| KeyF12 | KeyLeftShift | KeyLeftControl | KeyLeftAlt | KeyLeftSuper | KeyRightShift
| KeyRightControl | KeyRightAlt | KeyRightSuper | KeyMenu
| KeyOther : nat -> rl_key.

(** The raylib key code for a named key. *)
Definition key_code (k : rl_key) : nat :=
  match k with
  | KeyA => 65 | KeyB => 66 | KeyC => 67 | KeyD => 68
  | KeyE => 69 | KeyF => 70 | KeyG => 71 | KeyH => 72
  | KeyI => 73 | KeyJ => 74 | KeyK => 75 | KeyL => 76
  | KeyM => 77 | KeyN => 78 | KeyO => 79 | KeyP => 80
  | KeyQ => 81 | KeyR => 82 | KeyS => 83 | KeyT => 84
  | KeyU => 85 | KeyV => 86 | KeyW => 87 | KeyX => 88
  | KeyY => 89 | KeyZ => 90 | KeyNum0 => 48 | KeyNum1 => 49
  | KeyNum2 => 50 | KeyNum3 => 51 | KeyNum4 => 52 | KeyNum5 => 53
  | KeyNum6 => 54 | KeyNum7 => 55 | KeyNum8 => 56 | KeyNum9 => 57
  | KeySpace => 32 | KeyApostrophe => 39 | KeyComma => 44 | KeyMinus => 45
  | KeyPeriod => 46 | KeySlash => 47 | KeySemicolon => 59 | KeyEqual => 61
  | KeyLeftBracket => 91 | KeyBackslash => 92 | KeyRightBracket => 93 | KeyGrave => 96
  | KeyEscape => 256 | KeyEnter => 257 | KeyTab => 258 | KeyBackspace => 259
  | KeyInsert => 260 | KeyDelete => 261 | KeyRight => 262 | KeyLeft => 263
  | KeyDown => 264 | KeyUp => 265 | KeyPageUp => 266 | KeyPageDown => 267
  | KeyHome => 268 | KeyEnd => 269 | KeyCapsLock => 280 | KeyScrollLock => 281
  | KeyNumLock => 282 | KeyPrintScreen => 283 | KeyPause => 284 | KeyF1 => 290
  | KeyF2 => 291 | KeyF3 => 292 | KeyF4 => 293 | KeyF5 => 294
  | KeyF6 => 295 | KeyF7 => 296 | KeyF8 => 297 | KeyF9 => 298
  | KeyF10 => 299 | KeyF11 => 300 | KeyF12 => 301 | KeyLeftShift => 340
  | KeyLeftControl => 341 | KeyLeftAlt => 342 | KeyLeftSuper => 343 | KeyRightShift => 344
  | KeyRightControl => 345 | KeyRightAlt => 346 | KeyRightSuper => 347 | KeyMenu => 348
  | KeyOther n => n
  end.

(** Mouse buttons, in raylib's own order. *)
Inductive rl_button : Type :=
| ButtonLeft | ButtonRight | ButtonMiddle
| ButtonSide | ButtonExtra | ButtonForward | ButtonBack
| ButtonOther : nat -> rl_button.

(** The raylib button code for a named mouse button. *)
Definition button_code (b : rl_button) : nat :=
  match b with
  | ButtonLeft => 0 | ButtonRight => 1 | ButtonMiddle => 2
  | ButtonSide => 3 | ButtonExtra => 4 | ButtonForward => 5
  | ButtonBack => 6 | ButtonOther n => n
  end.

(** * Effects

    Every constructor takes flat scalars so that the C++ helper header stays
    independent of the struct names Crane generates for a given application.
    The smart constructors below restore the structured interface. *)

Inductive raylibE : Type -> Type :=
(** Window lifetime and geometry. *)
| InitWindow : PrimString.string -> nat -> nat -> raylibE unit
| CloseWindow : raylibE unit
| WindowShouldClose : raylibE bool
| SetTargetFPS : nat -> raylibE unit
| GetScreenSize : raylibE (nat * nat)
(** Frame boundaries. *)
| BeginDrawing : raylibE unit
| EndDrawing : raylibE unit
| ClearBackground : nat -> nat -> nat -> nat -> raylibE unit
(** Time and randomness. *)
| GetTime : raylibE R
| GetRandomValue : nat -> nat -> raylibE nat
(** Input. *)
| IsKeyPressed : nat -> raylibE bool
| IsKeyDown : nat -> raylibE bool
| IsButtonPressed : nat -> raylibE bool
| IsButtonDown : nat -> raylibE bool
| GetMousePosition : raylibE (R * R)
| GetMouseDelta : raylibE (R * R)
| GetMouseWheel : raylibE R
(** Two-dimensional drawing. *)
| DrawRectangle : R -> R -> R -> R -> R -> nat -> nat -> nat -> nat -> raylibE unit
| DrawText : PrimString.string -> R -> R -> nat -> nat -> nat -> nat -> nat ->
    raylibE unit
| MeasureText : PrimString.string -> nat -> raylibE nat
(** Three-dimensional drawing. *)
| BeginMode3D : R -> R -> R -> R -> R -> R -> R -> R -> R -> R -> raylibE unit
| EndMode3D : raylibE unit
| DrawCube : R -> R -> R -> R -> R -> R -> nat -> nat -> nat -> nat -> raylibE unit
| PushMatrix : raylibE unit
| PopMatrix : raylibE unit
| Rotate : R -> R -> R -> R -> raylibE unit
(** Off-screen targets. *)
| LoadRenderTexture : nat -> nat -> raylibE rl_texture
| UnloadRenderTexture : rl_texture -> raylibE unit
| BeginTextureMode : rl_texture -> raylibE unit
| EndTextureMode : raylibE unit
| DrawRenderTexture : rl_texture -> R -> R -> raylibE unit
(** Files. *)
| TakeScreenshot : PrimString.string -> raylibE unit
| FileExists : PrimString.string -> raylibE bool.

(** The effect functor itself is abstract; only its constructors extract. *)
Crane Extract Skip raylibE.

(** * Primitive operations

    One Rocq constant per effect, taking the same flat scalars, so that the
    extraction mappings never mention a generated struct or field name. *)

(** Open a window with the given title and size. *)
Definition rl_init_window {E} `{raylibE -< E}
    (title : PrimString.string) (w h : nat) : itree E unit :=
  embed (InitWindow title w h).

(** Close the window and release the graphics context. *)
Definition rl_close_window {E} `{raylibE -< E} : itree E unit := embed CloseWindow.

(** Whether the user asked to close the window this frame. *)
Definition rl_should_close {E} `{raylibE -< E} : itree E bool :=
  embed WindowShouldClose.

(** Ask the library to pace the frame loop at the given rate. *)
Definition rl_set_target_fps {E} `{raylibE -< E} (fps : nat) : itree E unit :=
  embed (SetTargetFPS fps).

(** The current drawable size of the window, in pixels. *)
Definition rl_screen_size {E} `{raylibE -< E} : itree E (nat * nat) :=
  embed GetScreenSize.

(** Begin a frame. Every draw call must sit between this and [rl_end_drawing]. *)
Definition rl_begin_drawing {E} `{raylibE -< E} : itree E unit := embed BeginDrawing.

(** End a frame and present it. *)
Definition rl_end_drawing {E} `{raylibE -< E} : itree E unit := embed EndDrawing.

(** Fill the current target with one straight RGBA color. *)
Definition rl_clear_rgba {E} `{raylibE -< E} (r g b a : nat) : itree E unit :=
  embed (ClearBackground r g b a).

(** Seconds elapsed since the window opened. *)
Definition rl_time {E} `{raylibE -< E} : itree E R := embed GetTime.

(** A uniformly chosen integer in an inclusive range. *)
Definition rl_random {E} `{raylibE -< E} (lo hi : nat) : itree E nat :=
  embed (GetRandomValue lo hi).

(** Whether a raw key code went down during this frame. *)
Definition rl_code_pressed {E} `{raylibE -< E} (code : nat) : itree E bool :=
  embed (IsKeyPressed code).

(** Whether a raw key code is held right now. *)
Definition rl_code_down {E} `{raylibE -< E} (code : nat) : itree E bool :=
  embed (IsKeyDown code).

(** Whether a raw mouse button code went down during this frame. *)
Definition rl_button_code_pressed {E} `{raylibE -< E} (code : nat) : itree E bool :=
  embed (IsButtonPressed code).

(** Whether a raw mouse button code is held right now. *)
Definition rl_button_code_down {E} `{raylibE -< E} (code : nat) : itree E bool :=
  embed (IsButtonDown code).

(** The cursor position in window coordinates. *)
Definition rl_mouse {E} `{raylibE -< E} : itree E (R * R) := embed GetMousePosition.

(** How far the cursor moved since the previous frame. *)
Definition rl_mouse_delta {E} `{raylibE -< E} : itree E (R * R) :=
  embed GetMouseDelta.

(** How far the wheel turned since the previous frame. *)
Definition rl_wheel {E} `{raylibE -< E} : itree E R := embed GetMouseWheel.

(** Fill a rectangle whose corners are rounded by the given fraction of its
    shorter side; a roundness of zero gives square corners. *)
Definition rl_rectangle_rgba {E} `{raylibE -< E}
    (x y w h roundness : R) (r g b a : nat) : itree E unit :=
  embed (DrawRectangle x y w h roundness r g b a).

(** Draw a line of text with its top-left corner at the given point. *)
Definition rl_text_rgba {E} `{raylibE -< E}
    (s : PrimString.string) (x y : R) (size r g b a : nat) : itree E unit :=
  embed (DrawText s x y size r g b a).

(** The width the given text would occupy at the given size. *)
Definition rl_text_width {E} `{raylibE -< E}
    (s : PrimString.string) (size : nat) : itree E nat :=
  embed (MeasureText s size).

(** Enter three-dimensional drawing through a camera given componentwise. *)
Definition rl_begin_3d_at {E} `{raylibE -< E}
    (px py pz tx ty tz ux uy uz fovy : R) : itree E unit :=
  embed (BeginMode3D px py pz tx ty tz ux uy uz fovy).

(** Leave three-dimensional drawing. *)
Definition rl_end_3d {E} `{raylibE -< E} : itree E unit := embed EndMode3D.

(** Draw an axis-aligned box given componentwise. *)
Definition rl_cube_rgba {E} `{raylibE -< E}
    (x y z w h d : R) (r g b a : nat) : itree E unit :=
  embed (DrawCube x y z w h d r g b a).

(** Save the current transform. *)
Definition rl_push {E} `{raylibE -< E} : itree E unit := embed PushMatrix.

(** Restore the transform saved by the matching [rl_push]. *)
Definition rl_pop {E} `{raylibE -< E} : itree E unit := embed PopMatrix.

(** Rotate the current transform by an angle in degrees about an axis. *)
Definition rl_rotate_about {E} `{raylibE -< E} (degrees x y z : R) : itree E unit :=
  embed (Rotate degrees x y z).

(** Allocate an off-screen target of the given pixel size. *)
Definition rl_load_target {E} `{raylibE -< E} (w h : nat) : itree E rl_texture :=
  embed (LoadRenderTexture w h).

(** Release an off-screen target. *)
Definition rl_unload_target {E} `{raylibE -< E} (t : rl_texture) : itree E unit :=
  embed (UnloadRenderTexture t).

(** Direct subsequent drawing into an off-screen target. *)
Definition rl_begin_target {E} `{raylibE -< E} (t : rl_texture) : itree E unit :=
  embed (BeginTextureMode t).

(** Direct subsequent drawing back to the window. *)
Definition rl_end_target {E} `{raylibE -< E} : itree E unit := embed EndTextureMode.

(** Blit an off-screen target with its top-left corner at the given point. *)
Definition rl_draw_target {E} `{raylibE -< E} (t : rl_texture) (x y : R)
  : itree E unit := embed (DrawRenderTexture t x y).

(** Write the presented frame to an image file. *)
Definition rl_screenshot {E} `{raylibE -< E} (path : PrimString.string)
  : itree E unit := embed (TakeScreenshot path).

(** Whether a path names an existing file. *)
Definition rl_file_exists {E} `{raylibE -< E} (path : PrimString.string)
  : itree E bool := embed (FileExists path).

(** * Structured interface

    The same primitives with the record types restored. Keys and buttons have
    no wrapper here: [key_code] and [button_code] are pure, so an application
    writes [rl_code_pressed (key_code KeyU)] directly. *)

(** Fill the current target with one color. *)
Definition rl_clear {E} `{raylibE -< E} (c : rl_color) : itree E unit :=
  rl_clear_rgba (cr c) (cg c) (cb c) (ca c).

(** Fill a rounded rectangle. *)
Definition rl_rectangle {E} `{raylibE -< E}
    (r : rl_rect) (roundness : R) (c : rl_color) : itree E unit :=
  rl_rectangle_rgba (rx r) (ry r) (rw r) (rh r) roundness
                    (cr c) (cg c) (cb c) (ca c).

(** Draw a line of text. *)
Definition rl_text {E} `{raylibE -< E}
    (s : PrimString.string) (x y : R) (size : nat) (c : rl_color) : itree E unit :=
  rl_text_rgba s x y size (cr c) (cg c) (cb c) (ca c).

(** Enter three-dimensional drawing through the given camera. *)
Definition rl_begin_3d {E} `{raylibE -< E} (c : rl_camera) : itree E unit :=
  rl_begin_3d_at (v3x (cam_at c)) (v3y (cam_at c)) (v3z (cam_at c))
                 (v3x (cam_to c)) (v3y (cam_to c)) (v3z (cam_to c))
                 (v3x (cam_up c)) (v3y (cam_up c)) (v3z (cam_up c))
                 (cam_fovy c).

(** Draw an axis-aligned box centered at [centre] with the given extent. *)
Definition rl_cube {E} `{raylibE -< E}
    (centre size : rl_vec3) (c : rl_color) : itree E unit :=
  rl_cube_rgba (v3x centre) (v3y centre) (v3z centre)
               (v3x size) (v3y size) (v3z size) (cr c) (cg c) (cb c) (ca c).

(** Rotate the current transform about an axis vector. *)
Definition rl_rotate {E} `{raylibE -< E} (degrees : R) (axis : rl_vec3)
  : itree E unit := rl_rotate_about degrees (v3x axis) (v3y axis) (v3z axis).
