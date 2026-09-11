(** * Generic raylib bindings: extraction to C++

    Re-exports [RaylibDefs.v] and maps its effects onto the thin inline
    wrappers in [raylib_helpers.h]. Splitting the mappings out keeps the
    definitions usable under any extraction flavor. *)

From Crane Require Import Mapping.Std Mapping.NatIntStd Mapping.DequeList
  Mapping.ZInt Mapping.Real Monads.ITree.
From Crane Require Extraction.
From Rubik Require Export native.RaylibDefs.

(** The off-screen target handle is whatever the helper header calls it. *)
Crane Extract Inlined Constant rl_texture => "rl_texture" From "raylib_helpers.h".

(** Font handles and their lifetime. *)
Crane Extract Inlined Constant rl_font => "rl_font" From "raylib_helpers.h".
Crane Extract Inlined Constant rl_load_font =>
  "rl_load_font(%a0, %a1)" From "raylib_helpers.h".
Crane Extract Inlined Constant rl_unload_font =>
  "rl_unload_font(%a0)" From "raylib_helpers.h".

(** Window lifetime and geometry. *)
Crane Extract Inlined Constant rl_init_window =>
  "rl_init_window(%a0, %a1, %a2)" From "raylib_helpers.h".
Crane Extract Inlined Constant rl_close_window =>
  "rl_close_window()" From "raylib_helpers.h".
Crane Extract Inlined Constant rl_should_close =>
  "rl_should_close()" From "raylib_helpers.h".
Crane Extract Inlined Constant rl_set_target_fps =>
  "rl_set_target_fps(%a0)" From "raylib_helpers.h".
Crane Extract Inlined Constant rl_screen_size =>
  "rl_screen_size()" From "raylib_helpers.h".

(** Frame boundaries. *)
Crane Extract Inlined Constant rl_begin_drawing =>
  "rl_begin_drawing()" From "raylib_helpers.h".
Crane Extract Inlined Constant rl_end_drawing =>
  "rl_end_drawing()" From "raylib_helpers.h".
Crane Extract Inlined Constant rl_clear_rgba =>
  "rl_clear(%a0, %a1, %a2, %a3)" From "raylib_helpers.h".

(** Time and randomness. *)
Crane Extract Inlined Constant rl_time => "rl_time()" From "raylib_helpers.h".
Crane Extract Inlined Constant rl_random =>
  "rl_random(%a0, %a1)" From "raylib_helpers.h".

(** Input. *)
Crane Extract Inlined Constant rl_code_pressed =>
  "rl_key_pressed(%a0)" From "raylib_helpers.h".
Crane Extract Inlined Constant rl_code_down =>
  "rl_key_down(%a0)" From "raylib_helpers.h".
Crane Extract Inlined Constant rl_button_code_pressed =>
  "rl_button_pressed(%a0)" From "raylib_helpers.h".
Crane Extract Inlined Constant rl_button_code_down =>
  "rl_button_down(%a0)" From "raylib_helpers.h".
Crane Extract Inlined Constant rl_mouse => "rl_mouse()" From "raylib_helpers.h".
Crane Extract Inlined Constant rl_mouse_delta =>
  "rl_mouse_delta()" From "raylib_helpers.h".
Crane Extract Inlined Constant rl_wheel => "rl_wheel()" From "raylib_helpers.h".

(** Two-dimensional drawing. *)
Crane Extract Inlined Constant rl_rectangle_rgba =>
  "rl_rectangle(%a0, %a1, %a2, %a3, %a4, %a5, %a6, %a7, %a8)"
  From "raylib_helpers.h".
Crane Extract Inlined Constant rl_text_rgba =>
  "rl_text(%a0, %a1, %a2, %a3, %a4, %a5, %a6, %a7, %a8, %a9)"
  From "raylib_helpers.h".
Crane Extract Inlined Constant rl_text_width =>
  "rl_text_width(%a0, %a1, %a2, %a3)" From "raylib_helpers.h".

(** Three-dimensional drawing. *)
Crane Extract Inlined Constant rl_begin_3d_at =>
  "rl_begin_3d(%a0, %a1, %a2, %a3, %a4, %a5, %a6, %a7, %a8, %a9)"
  From "raylib_helpers.h".
Crane Extract Inlined Constant rl_end_3d => "rl_end_3d()" From "raylib_helpers.h".
Crane Extract Inlined Constant rl_cube_rgba =>
  "rl_cube(%a0, %a1, %a2, %a3, %a4, %a5, %a6, %a7, %a8, %a9)"
  From "raylib_helpers.h".
Crane Extract Inlined Constant rl_push => "rl_push()" From "raylib_helpers.h".
Crane Extract Inlined Constant rl_pop => "rl_pop()" From "raylib_helpers.h".
Crane Extract Inlined Constant rl_rotate_about =>
  "rl_rotate(%a0, %a1, %a2, %a3)" From "raylib_helpers.h".

(** Off-screen targets. *)
Crane Extract Inlined Constant rl_load_target =>
  "rl_load_target(%a0, %a1)" From "raylib_helpers.h".
Crane Extract Inlined Constant rl_unload_target =>
  "rl_unload_target(%a0)" From "raylib_helpers.h".
Crane Extract Inlined Constant rl_begin_target =>
  "rl_begin_target(%a0)" From "raylib_helpers.h".
Crane Extract Inlined Constant rl_end_target =>
  "rl_end_target()" From "raylib_helpers.h".
Crane Extract Inlined Constant rl_draw_target =>
  "rl_draw_target(%a0, %a1, %a2)" From "raylib_helpers.h".

(** Files. *)
Crane Extract Inlined Constant rl_screenshot =>
  "rl_screenshot(%a0)" From "raylib_helpers.h".
Crane Extract Inlined Constant rl_file_exists =>
  "rl_file_exists(%a0)" From "raylib_helpers.h".

(** The structured wrappers, mapped through the same helpers so that no
    polymorphic Rocq body is ever generated for them. *)
Crane Extract Inlined Constant rl_clear =>
  "rl_clear(%a0.cr, %a0.cg, %a0.cb, %a0.ca)" From "raylib_helpers.h".
Crane Extract Inlined Constant rl_rectangle =>
  "rl_rectangle(%a0.rx, %a0.ry, %a0.rw, %a0.rh, %a1, %a2.cr, %a2.cg, %a2.cb, %a2.ca)"
  From "raylib_helpers.h".
Crane Extract Inlined Constant rl_text =>
  "rl_text(%a0, %a1, %a2, %a3, %a4, %a5, %a6.cr, %a6.cg, %a6.cb, %a6.ca)"
  From "raylib_helpers.h".
Crane Extract Inlined Constant rl_begin_3d =>
  "rl_begin_3d(%a0.cam_at.v3x, %a0.cam_at.v3y, %a0.cam_at.v3z, %a0.cam_to.v3x, %a0.cam_to.v3y, %a0.cam_to.v3z, %a0.cam_up.v3x, %a0.cam_up.v3y, %a0.cam_up.v3z, %a0.cam_fovy)"
  From "raylib_helpers.h".
Crane Extract Inlined Constant rl_cube =>
  "rl_cube(%a0.v3x, %a0.v3y, %a0.v3z, %a1.v3x, %a1.v3y, %a1.v3z, %a2.cr, %a2.cg, %a2.cb, %a2.ca)"
  From "raylib_helpers.h".
Crane Extract Inlined Constant rl_rotate =>
  "rl_rotate(%a0, %a1.v3x, %a1.v3y, %a1.v3z)" From "raylib_helpers.h".
