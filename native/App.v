(** * The Rubik viewer, written in Rocq

    Everything the user sees and does lives here: the palette, the panel
    layout, hit testing, the orbit camera, the turn animation, and the frame
    loop. The native side only provides raylib primitives and a worker thread,
    so no cube state, no layout, and no timing decision is made in C++. *)

From Corelib Require Import PrimString.
From Stdlib Require Import Arith List Reals.
From Crane Require Import Mapping.Std Mapping.NatIntStd
  Mapping.ZInt Mapping.Real Monads.ITree.
From Rubik Require Import Cube.BasicRubik Viewer Native.Bindings.Raylib
  Native.Bindings.Job Native.Bindings.Proc.
Import ListNotations ITreeNotations.
Local Open Scope pstring_scope.
Local Open Scope itree_scope.

(** The viewer needs raylib for its window and one background job for its
    solver; neither binding knows about the other. *)
Local Notation appE := (raylibE +' jobE +' procE).

(** A search in flight: the certified solver, run off the drawing thread. *)
Definition search : Type := job (option (list nat)).

(** Named keys and buttons, at this application's effect type. *)
Definition pressed (k : rl_key) : itree appE bool := rl_code_pressed (key_code k).

(** Whether a key is down this frame, as opposed to newly pressed. *)
Definition held (k : rl_key) : itree appE bool := rl_code_down (key_code k).

(** Whether a mouse button went down this frame, *)
Definition clicked (b : rl_button) : itree appE bool :=
  rl_button_code_pressed (button_code b).

(** and whether it is being held. *)
Definition dragging (b : rl_button) : itree appE bool :=
  rl_button_code_down (button_code b).

(** Whether any of the given keys is held right now. *)
Fixpoint any_held (ks : list rl_key) : itree appE bool :=
  match ks with
  | [] => Ret false
  | k :: rest => down <- held k ;; if down : bool then Ret true else any_held rest
  end.

(** * Text *)

(** One decimal digit as text. *)
Definition digit_text (d : nat) : PrimString.string :=
  match d with
  | 0 => "0" | 1 => "1" | 2 => "2" | 3 => "3" | 4 => "4"
  | 5 => "5" | 6 => "6" | 7 => "7" | 8 => "8" | _ => "9"
  end.

(** Decimal digits of a number, most significant first, with fuel to recurse. *)
Fixpoint nat_text_aux (fuel n : nat) : PrimString.string :=
  match fuel with
  | 0 => ""
  | S rest =>
      if Nat.ltb n 10 then digit_text n
      else PrimString.cat (nat_text_aux rest (Nat.div n 10))
                          (digit_text (Nat.modulo n 10))
  end.

(** The letter of a face, in the model's U/R/F/D/L/B order. *)
Definition face_text (f : nat) : PrimString.string :=
  match f with
  | 0 => "U" | 1 => "R" | 2 => "F" | 3 => "D" | 4 => "L" | _ => "B"
  end.

(** The suffix that distinguishes half and counter-clockwise turns. *)
Definition amount_text (t : nat) : PrimString.string :=
  match t with 0 => "" | 1 => "2" | _ => "'" end.

(** One move in standard notation. *)
Definition move_text (c : nat) : PrimString.string :=
  PrimString.cat (face_text (Nat.div c 3)) (amount_text (Nat.modulo c 3)).

(** A sequence of moves, separated by spaces. *)
Fixpoint moves_join (cs : list nat) : PrimString.string :=
  match cs with
  | [] => ""
  | [c] => move_text c
  | c :: rest => PrimString.cat (move_text c)
                   (PrimString.cat "  " (moves_join rest))
  end.

(** A pending solution, or a dash when there is nothing to play. *)
Definition moves_text (cs : list nat) : PrimString.string :=
  match cs with [] => "-" | _ => moves_join cs end.

(** The sentence shown under the search controls. *)
Definition status_text (st : nat) (pending : list nat) : PrimString.string :=
  match st with
  | 1 => "Searching - keep exploring the view"
  | 2 => match pending with
         | [] => "Already solved. No moves needed."
         | _ => "Solution found"
         end
  | 3 => "Solved. Nicely done."
  | 4 => "No solution found. Reset the cube."
  | 6 => "Result rejected. Please try again."
  | _ => "Turn a face, or try a short scramble."
  end.

(** * Palette *)

(** The window and the 3D backdrop behind the cube: a warm off-white, so the
    cube's black joints carry the contrast rather than the ground. *)
Definition background : rl_color := rgb 242 242 236.

(** Recessed areas inside the dark panel, which keep the old dark ground. *)
Definition sunken : rl_color := rgb 15 21 32.

(** The panel's own ground, dark against the light page. *)
Definition panel_fill : rl_color := rgb 24 33 47.

(** A button at rest, *)
Definition raised : rl_color := rgb 36 48 65.

(** and one under the pointer. *)
Definition hovered : rl_color := rgb 48 66 87.

(** Secondary text, for hints and labels. *)
Definition muted : rl_color := rgb 147 165 187.

(** Primary text. *)
Definition ink : rl_color := rgb 235 241 249.

(** The one saturated colour, for the selected turn amount. *)
Definition accent : rl_color := rgb 84 217 195.
(** The cube's body, seen through the gaps between stickers and around its
    silhouette. Black so the joints read against the light backdrop. *)
Definition cubie_ink : rl_color := rgb 0 0 0.

(** Sticker colors in U/R/F/D/L/B order, with white down, blue front, and red right.
    Swapping both U/D and F/B preserves the physical color scheme's handedness. *)
Definition palette : list rl_color :=
  [rgb 247 201 60; rgb 226 60 71; rgb 56 127 230;
   rgb 241 244 239; rgb 246 133 48; rgb 45 186 118].

(** The color of one sticker code. *)
Definition sticker_color (n : nat) : rl_color := nth n palette ink.

(** * Layout

    The window is a fixed size, so every rectangle is a constant. *)

Definition window_w : nat := 1200.

(** and its height. *)
Definition window_h : nat := 688.

(** Pixel size of the off-screen target that holds the 3D view. *)
Definition canvas_w : nat := 868.

(** and its height. *)
Definition canvas_h : nat := 640.

(** Where that target is blitted in the window. The canvas and the panel end
    at the same line, so the window has no strip left over below them. *)
Definition canvas : rl_rect := Rect 20 24 868 640.

(** The side panel and the left edge of its contents. *)
Definition panel_box : rl_rect := Rect 900 24 280 640.

(** Where the panel starts, in window pixels. *)
Definition panel_x : R := 916.

(** One shared track makes the mutually exclusive turn amounts a segmented control. *)
Definition amount_track : rl_rect := Rect 916 66 248 36.

(** * Buttons *)

(** A control is one rectangle, one label, and the command it issues. *)
Record button : Type := Button {
  b_box : rl_rect;
  b_text : PrimString.string;
  b_cmd : nat;
  b_live : bool;
  b_sel : bool
}.

(** Commands at or above this value only change the panel, never the cube. *)
Definition panel_command : nat := 100.

(** The three turn amounts that arm the face buttons. *)
Definition amount_button (i : nat) (busy : bool) (turn : nat) : button :=
  Button (Rect (panel_x + 4 + INR i * 80)%R 70 80 28)
         (nth i ["CW"; "180"; "CCW"] "") (panel_command + i)
         (negb busy) (Nat.eqb turn i).

(** One face button, issuing that face with the armed amount. *)
Definition face_button (i : nat) (busy : bool) (turn : nat) : button :=
  Button (Rect (panel_x + INR (Nat.modulo i 3) * 85)%R
               (114 + INR (Nat.div i 3) * 40)%R 78 32)
         (face_text i) (1 + 3 * i + turn) (negb busy) false.

(** Every control in the side panel, in drawing and hit-testing order. *)
Definition buttons (busy playing has_plan : bool) (turn : nat)
  : list button :=
  map (fun i => amount_button i busy turn) [0; 1; 2] ++
  map (fun i => face_button i busy turn) [0; 1; 2; 3; 4; 5] ++
  [Button (Rect 916 196 120 32) "Undo" 24 (negb busy) false;
   Button (Rect 1044 196 120 32) "Reset cube" 20 true false;
   Button (Rect 916 238 248 34) "Scramble / 20 turns" 19 (negb busy) false;
   Button (Rect 916 282 248 38)
     (if busy then "Cancel search" else "Solve")
     (if busy then 27 else 21) true false;
   Button (Rect 916 482 120 32) "Step" 22 (andb (negb busy) has_plan) false;
   Button (Rect 1044 482 120 32) (if playing then "Pause" else "Play") 23
     (andb (negb busy) has_plan) false].

(** The first live control under the cursor, if any. *)
Fixpoint hit (bs : list button) (x y : R) : option button :=
  match bs with
  | [] => None
  | b :: rest =>
      if andb (b_live b) (in_rect x y (b_box b)) then Some b else hit rest x y
  end.

(** * Camera *)

(** The orientation the user controls with the mouse, carried as the camera's
    own axes rather than as a heading and an elevation. A heading and an
    elevation have poles: at the top and the bottom the orbit radius collapses,
    the eye stops moving, and the up direction lines up with the view. Carrying
    the axes has no poles, so the cube turns the same way from every attitude
    and never runs out of travel. *)
Record orbit : Type := Orbit {
  o_right : rl_vec3;  (** screen right *)
  o_up : rl_vec3;     (** screen up *)
  o_back : rl_vec3;   (** from the cube towards the eye *)
  o_dist : R          (** how far the eye sits from the cube *)
}.

(** Keep a real between two bounds. *)
Definition clampR (lo hi x : R) : R :=
  if Rlt_dec x lo then lo else if Rlt_dec hi x then hi else x.

(** Rebuild an exactly orthonormal, right-handed triple from a drifted one.
    Thousands of small turns accumulate rounding, and this costs three square
    roots a frame to keep the view from slowly shearing. *)
Definition orthonormal (right up back : rl_vec3) (d : R) : orbit :=
  let b := v3_unit back in
  let r := v3_unit (v3_cross up b) in
  Orbit r (v3_cross b r) b d.

(** Build the starting attitude from a heading and an elevation, which is a
    convenient way to name one view even though the camera does not store it. *)
Definition attitude (yaw pitch d : R) : orbit :=
  orthonormal (Vec3 0 0 0)
              (Vec3 0 1 0)
              (Vec3 (cos pitch * sin yaw)%R (sin pitch)%R (cos pitch * cos yaw)%R)
              d.

(** The three-quarter view the cube starts and recenters at. *)
Definition home_orbit : orbit := attitude 0.65 0.48 9.2.

(** Turn the axes about the camera's own up direction, which leaves it fixed
    and swings the other two round in their shared plane. *)
Definition spin (o : orbit) (angle : R) : orbit :=
  let c := cos angle in
  let s := sin angle in
  orthonormal (v3_add (v3_scale c (o_right o)) (v3_scale (-s)%R (o_back o)))
              (o_up o)
              (v3_add (v3_scale c (o_back o)) (v3_scale s (o_right o)))
              (o_dist o).

(** Turn the axes about the camera's own right direction. *)
Definition tilt (o : orbit) (angle : R) : orbit :=
  let c := cos angle in
  let s := sin angle in
  orthonormal (o_right o)
              (v3_add (v3_scale c (o_up o)) (v3_scale s (o_back o)))
              (v3_add (v3_scale c (o_back o)) (v3_scale (-s)%R (o_up o)))
              (o_dist o).

(** Drag turns the view, the wheel moves the eye in and out. Nothing about the
    turning is bounded: the cube follows the mouse from any attitude, in any
    direction, for as long as the drag lasts. *)
Definition turn_orbit (o : orbit) (dx dy wheel : R) : orbit :=
  let turned := tilt (spin o (-(dx * 0.008))%R) (-(dy * 0.008))%R in
  Orbit (o_right turned) (o_up turned) (o_back turned)
        (clampR 5.5 15 (o_dist o - wheel * 0.55)%R).

(** Place the eye along the camera's own back direction and look at the cube. *)
Definition orbit_camera (o : orbit) : rl_camera :=
  Camera (v3_scale (o_dist o) (o_back o)) (Vec3 0 0 0) (o_up o) 37.

(** * The cube in space *)

(** Outward face normals in the +x right, +y up, +z front frame of Geometry.v. *)
Definition face_axis (f : nat) : rl_vec3 :=
  match f with
  | 0 => Vec3 0 1 0
  | 1 => Vec3 1 0 0
  | 2 => Vec3 0 0 1
  | 3 => Vec3 0 (-1) 0
  | 4 => Vec3 (-1) 0 0
  | _ => Vec3 0 0 (-1)
  end.

(** Row and column indices run zero to two; cube coordinates run minus one to one. *)
Definition coord (i : nat) : R := (INR i - 1)%R.

(** How far a sticker sits outside the centre of its cubie. *)
Definition sticker_edge : R := 1.489.

(** Place a sticker of one face, or its cubie when [out] is one. *)
Definition place (f row col : nat) (out : R) : rl_vec3 :=
  let r := coord row in
  let c := coord col in
  match f with
  | 0 => Vec3 c out r
  | 1 => Vec3 out (-r) (-c)
  | 2 => Vec3 c (-r) out
  | 3 => Vec3 c (-out) (-r)
  | 4 => Vec3 (-out) (-r) c
  | _ => Vec3 (-c) (-r) (-out)
  end.

(** A sticker is a thin slab facing outward from its cubie. *)
Definition sticker_size (f : nat) : rl_vec3 :=
  match f with
  | 0 => Vec3 0.86 0.018 0.86
  | 3 => Vec3 0.86 0.018 0.86
  | 1 => Vec3 0.018 0.86 0.86
  | 4 => Vec3 0.018 0.86 0.86
  | _ => Vec3 0.86 0.86 0.018
  end.

(** The dot product of two vectors. *)
Definition dot (a b : rl_vec3) : R :=
  (v3x a * v3x b + v3y a * v3y b + v3z a * v3z b)%R.

(** A face turn carries exactly the cubies on that face's side of the centre. *)
Definition in_layer (v : rl_vec3) (f : nat) : bool :=
  if Rlt_dec 0.5 (dot v (face_axis f)) then true else false.

(** With no turn in flight every cubie is drawn once; otherwise the turning
    half and the resting half are drawn in separate passes. *)
Definition selected (layer : option nat) (moving : bool) (v : rl_vec3) : bool :=
  match layer with
  | None => negb moving
  | Some f => Bool.eqb (in_layer v f) moving
  end.

(** The three rows or columns of a face, *)
Definition thirds : list nat := [0; 1; 2].

(** and the six faces in the model's order. *)
Definition faces_in_order : list nat := [0; 1; 2; 3; 4; 5].

(** The twenty-seven cubie centres. *)
Definition cubies : list rl_vec3 :=
  flat_map (fun x => flat_map (fun y => map (fun z => Vec3 (coord x) (coord y) (coord z))
                                            thirds) thirds) thirds.

(** Where one sticker's color sits in a 54-number snapshot. *)
Definition sticker_index (f row col : nat) : nat := f * 9 + row * 3 + col.

(** * Animation *)

(** A turn in flight: which face, how far it travels, and when it started. *)
Record anim : Type := Anim { an_face : nat; an_sweep : R; an_start : R; an_len : R }.

(** Clockwise from outside is a negative rotation about the outward axis. *)
Definition sweep_of (t : nat) : R :=
  match t with 0 => -90 | 1 => -180 | _ => 90 end.

(** Half turns travel twice as far, so they are given a little more time. *)
Definition length_of (t : nat) : R := match t with 1 => 0.22 | _ => 0.15 end.

(** Smoothstep keeps the layer from starting and stopping abruptly. *)
Definition ease (p : R) : R := (p * p * (3 - 2 * p))%R.

(** How far the turning layer has travelled by now. *)
Definition anim_angle (a : anim) (now : R) : R :=
  (an_sweep a * ease (clampR 0 1 ((now - an_start a) / an_len a)))%R.

(** Whether a turn started before now is still in flight. *)
Definition anim_running (a : anim) (now : R) : bool :=
  if Rlt_dec (now - an_start a)%R (an_len a) then true else false.

(** Inverting a move keeps its face and swaps clockwise with counter-clockwise. *)
Definition inverse_code (c : nat) : nat := 3 * (Nat.div c 3) + (2 - Nat.modulo c 3).

(** Equality of two move-code or color lists. *)
Fixpoint list_eqb (a b : list nat) : bool :=
  match a, b with
  | [], [] => true
  | x :: xs, y :: ys => andb (Nat.eqb x y) (list_eqb xs ys)
  | _, _ => false
  end.

(** The move pushed onto a history, when exactly one was. *)
Definition pushed (before after : list nat) : option nat :=
  match after with
  | c :: rest => if list_eqb rest before then Some c else None
  | [] => None
  end.

(** One applied turn is one move pushed onto, or popped from, the undo history;
    resets and scrambles change it by more than that and are shown at once. *)
Definition single_turn (before after : list nat) : option nat :=
  match pushed before after with
  | Some c => Some c
  | None => match pushed after before with
            | Some d => Some (inverse_code d)
            | None => None
            end
  end.

(** What the screen is showing, which trails the model while a turn sweeps. *)
Record shown : Type :=
  Shown { s_colors : list nat; s_past : list nat; s_anim : option anim }.

(** Catch the display up to the model, starting a sweep for a single new turn. *)
Definition advance (s : shown) (v : view) (now : R) : shown :=
  let past := map move_code (history v) in
  let colors := colors_of (cube v) in
  match s_anim s with
  | Some a =>
      if anim_running a now then Shown (s_colors s) past (Some a)
      else Shown colors past None
  | None =>
      if Nat.eqb (length (s_colors s)) 0 then Shown colors past None
      else match single_turn (s_past s) past with
           | Some c =>
               if list_eqb colors (s_colors s) then Shown colors past None
               else Shown (s_colors s) past
                      (Some (Anim (Nat.div c 3) (sweep_of (Nat.modulo c 3)) now
                                  (length_of (Nat.modulo c 3))))
           | None => Shown colors past None
           end
  end.

(** * Application state *)

(** Panel and camera state that input updates and drawing reads. *)
Record ui : Type :=
  Ui { u_orbit : orbit; u_drag : bool; u_turn : nat; u_step_at : R }.

(** Progress of the scripted self-test, when one is running. *)
Record script : Type := Script { k_stage : nat; k_frames : nat; k_ok : bool }.

(** The whole viewer: the certified cube, the panel, what is on screen, and
    the search running behind it, if any. *)
Record app : Type := Mk {
  a_view : view;
  a_job : option search;
  a_ui : ui;
  a_shown : shown;
  a_script : script
}.

(** Resources for one run: the target, fonts, and optional self-test output. *)
Record config : Type :=
  Config {
    c_target : rl_texture;
    c_regular : rl_font;
    c_semibold : rl_font;
    c_shot : option PrimString.string;
    (** Device pixels per layout pixel. One on a display raylib already
        handles; two where it does not, as in a browser on a dense screen. *)
    c_scale : nat
  }.

(** Use regular text for guidance and semibold for titles, controls, and moves. *)
Definition label (cfg : config) (strong : bool) (s : PrimString.string)
    (x y : R) (size : nat) (color : rl_color) : itree appE unit :=
  rl_text (if strong then c_semibold cfg else c_regular cfg) s x y size 0.3 color.

(** * Drawing *)

(** Run an effect for each element of a list, in order. *)
Fixpoint for_each {A} (xs : list A) (f : A -> itree appE unit) : itree appE unit :=
  match xs with
  | [] => Ret tt
  | x :: rest => f x ;; for_each rest f
  end.

(** Draw the resting or the turning half of the cube's black body. *)
Definition draw_cubies (layer : option nat) (moving : bool) : itree appE unit :=
  for_each cubies (fun v =>
    if selected layer moving v
    then rl_cube v (Vec3 0.97 0.97 0.97) cubie_ink
    else Ret tt).

(** Draw the stickers of one half, reading colors from a snapshot. *)
Definition draw_stickers (colors : list nat) (layer : option nat) (moving : bool)
  : itree appE unit :=
  for_each faces_in_order (fun f =>
    for_each thirds (fun row =>
      for_each thirds (fun col =>
        if selected layer moving (place f row col 1)
        then rl_cube (place f row col sticker_edge) (sticker_size f)
               (sticker_color (nth (sticker_index f row col) colors 0))
        else Ret tt))).

(** Draw one half of the cube. *)
Definition draw_half (colors : list nat) (layer : option nat) (moving : bool)
  : itree appE unit :=
  draw_cubies layer moving ;; draw_stickers colors layer moving.

(** Draw the cube, sweeping one layer when a turn is in flight. *)
Definition draw_cube_now (colors : list nat) (a : option anim) (now : R)
  : itree appE unit :=
  match a with
  | None => draw_half colors None false
  | Some an =>
      draw_half colors (Some (an_face an)) false ;;
      rl_push ;;
      rl_rotate (anim_angle an now) (face_axis (an_face an)) ;;
      draw_half colors (Some (an_face an)) true ;;
      rl_pop
  end.

(** Render the cube into the off-screen target. The target is as many pixels
    across as the display is dense, so blitting it needs no scaling. *)
Definition draw_scene (cfg : config) (o : orbit) (s : shown) (now : R)
  : itree appE unit :=
  rl_begin_target (c_target cfg) ;;
  rl_clear background ;;
  rl_begin_3d (orbit_camera o) ;;
  draw_cube_now (s_colors s) (s_anim s) now ;;
  rl_end_3d ;;
  rl_end_target.

(** Blit it where the layout says, in device pixels, so it lands one for one. *)
Definition blit_scene (cfg : config) : itree appE unit :=
  let k := INR (c_scale cfg) in
  rl_draw_target (c_target cfg) (rx canvas * k) (ry canvas * k).

(** Draw one control, centring its label and dimming it when it is not live. *)
Definition draw_button (cfg : config) (mx my : R) (b : button) : itree appE unit :=
  let over := andb (b_live b) (in_rect mx my (b_box b)) in
  let segment := Nat.leb panel_command (b_cmd b) in
  let fill := if b_sel b then accent else if over then hovered else raised in
  let text_color := if b_sel b then sunken else if b_live b then ink else muted in
  (if andb segment (negb (orb (b_sel b) over)) then Ret tt
   else rl_rectangle (b_box b) 0.22
          (if b_live b then fill else fade fill 35 100)) ;;
  w <- rl_text_width (c_semibold cfg) (b_text b) 17 0.3 ;;
  label cfg true (b_text b)
          (rx (b_box b) + (rw (b_box b) - INR w) / 2)%R
          (ry (b_box b) + (rh (b_box b) - 17) / 2)%R 17
          (if b_live b then text_color else fade text_color 40 100).

(** Draw the whole frame: the cube, compact control panel, and input hints. *)
Definition draw (cfg : config) (a : app) (now : R) : itree appE unit :=
  let v := a_view a in
  let pending := map move_code (solution v) in
  let st := ui_state_code (status v) in
  let busy := searching v in
  p <- rl_mouse ;;
  let '(mx, my) := p in
  draw_scene cfg (u_orbit (a_ui a)) (a_shown a) now ;;
  rl_begin_drawing ;;
  rl_clear background ;;
  blit_scene cfg ;;
  rl_begin_2d (INR (c_scale cfg)) ;;
  rl_rectangle panel_box 0.06 panel_fill ;;
  label cfg true "FACE TURNS" panel_x 40 16 ink ;;
  rl_rectangle amount_track 0.3 sunken ;;
  for_each (buttons busy (playing v) (negb (Nat.eqb (length pending) 0))
                    (u_turn (a_ui a)))
           (draw_button cfg mx my) ;;
  label cfg false (status_text st pending) panel_x 336 16
          (if orb (Nat.eqb st 4) (Nat.eqb st 6) then sticker_color 4 else muted) ;;
  for_each [0; 1; 2; 3]
    (fun row =>
      let line := firstn 5 (skipn (5 * row) pending) in
      if andb (Nat.eqb (length line) 0) (negb (Nat.eqb row 0)) then Ret tt
      else label cfg true (moves_text line) panel_x (366 + 26 * INR row)%R 23 accent) ;;
  label cfg false "Home: white down, blue front" panel_x 534 14 muted ;;
  label cfg false "Red right. Drag orbits the view." panel_x 554 14 muted ;;
  label cfg false "Scroll to zoom. Home recenters." panel_x 582 14 muted ;;
  label cfg false "U R F D L B turn a face." panel_x 602 14 muted ;;
  label cfg false "Shift inverts, Alt half turns." panel_x 622 14
          (fade muted 70 100) ;;
  rl_end_2d ;;
  rl_end_drawing.

(** * Input *)

(** The face keys, in the model's U/R/F/D/L/B order. *)
Definition face_keys : list rl_key := [KeyU; KeyR; KeyF; KeyD; KeyL; KeyB].

(** Return the command of the first key in the list that went down. *)
Fixpoint first_pressed (ks : list (rl_key * nat)) : itree appE nat :=
  match ks with
  | [] => Ret 0
  | (k, cmd) :: rest =>
      down <- pressed k ;;
      if down : bool then Ret cmd else first_pressed rest
  end.

(** Pair each face key with the turn it issues at the given amount. *)
Definition face_key_commands (amount : nat) : list (rl_key * nat) :=
  combine face_keys (map (fun i => 1 + 3 * i + amount) faces_in_order).

(** The keys that drive the panel rather than the cube. *)
Definition panel_key_commands (busy : bool) : list (rl_key * nat) :=
  [(KeyS, 19); (KeyX, 20); (KeyEnter, if busy then 27 else 21);
   (KeySpace, 22); (KeyP, 23); (KeyBackspace, 24)].

(** Fold this frame's mouse motion into the camera. *)
Definition read_orbit (u : ui) : itree appE ui :=
  p <- rl_mouse ;;
  let '(mx, my) := p in
  let over := in_rect mx my canvas in
  lp <- clicked ButtonLeft ;;
  rp <- clicked ButtonRight ;;
  ld <- dragging ButtonLeft ;;
  rd <- dragging ButtonRight ;;
  d <- rl_mouse_delta ;;
  let '(dx, dy) := d in
  wheel <- rl_wheel ;;
  home <- pressed KeyHome ;;
  let drag := if orb ld rd then orb (andb (orb lp rp) over) (u_drag u) else false in
  let moved := turn_orbit (u_orbit u) (if drag then dx else 0)
                          (if drag then dy else 0) (if over then wheel else 0) in
  Ret (Ui (if home : bool then home_orbit else moved) drag (u_turn u) (u_step_at u)).

(** Read one command from the user, along with the panel state it changes. *)
Definition read_command (a : app) (u : ui) (now : R) : itree appE (nat * ui) :=
  let v := a_view a in
  let busy := searching v in
  let pending := negb (Nat.eqb (length (solution v)) 0) in
  p <- rl_mouse ;;
  let '(mx, my) := p in
  click <- clicked ButtonLeft ;;
  let armed := hit (buttons busy (playing v) pending (u_turn u)) mx my in
  match (if click : bool then armed else None) with
  | Some b =>
      if Nat.leb panel_command (b_cmd b)
      then Ret (0, Ui (u_orbit u) (u_drag u) (b_cmd b - panel_command) (u_step_at u))
      else Ret (b_cmd b, u)
  | None =>
      shift <- any_held [KeyLeftShift; KeyRightShift] ;;
      alt <- any_held [KeyLeftAlt; KeyRightAlt] ;;
      let amount := if shift : bool then 2 else if alt : bool then 1 else u_turn u in
      turn <- first_pressed (face_key_commands amount) ;;
      if negb (Nat.eqb turn 0) then Ret (turn, u)
      else
        key <- first_pressed (panel_key_commands busy) ;;
        if negb (Nat.eqb key 0) then Ret (key, u)
        else if andb (playing v)
                     (if Rlt_dec 0.4 (now - u_step_at u)%R then true else false)
        then Ret (29, Ui (u_orbit u) (u_drag u) (u_turn u) now)
        else Ret (0, u)
  end.

(** * The scripted self-test

    The same loop, driven from a fixed sequence instead of a keyboard, so the
    exported screenshot is produced by the real extracted program. *)

Definition script_command (cfg : config) (a : app) (now : R)
  : itree appE (nat * ui * script) :=
  let v := a_view a in
  let k := a_script a in
  let spun := turn_orbit (u_orbit (a_ui a)) 0.7 0
                 (if Nat.eqb (k_frames k) 2 then 0.5 else 0) in
  let u := Ui spun false (u_turn (a_ui a)) (u_step_at (a_ui a)) in
  let k1 := Script (k_stage k) (S (k_frames k)) (k_ok k) in
  let bump := Script (S (k_stage k)) (S (k_frames k)) (k_ok k) in
  if Nat.ltb 900 (k_frames k) then Ret (28, u, k1)
  (* Let the solved cube reach the screen, so the first turn has a snapshot
     to animate away from. *)
  else if Nat.ltb (k_frames k) 2 then Ret (0, u, k1)
  else match s_anim (a_shown a) with
  | Some _ => Ret (0, u, k1)
  | None =>
    (* Drive playback the way a person would, one move at a time. *)
    if andb (playing v) (if Rlt_dec 0.2 (now - u_step_at (a_ui a))%R
                         then true else false)
    then Ret (29, Ui spun false (u_turn u) now, k1)
    else
    match k_stage k with
    | 0 => Ret (4, u, bump)
    | 1 => Ret (1, u, bump)
    | 2 => Ret (21, u, bump)
    | 3 => if Nat.eqb (ui_state_code (status v)) 2 then Ret (23, u, bump)
           else Ret (0, u, k1)
    | 4 => if andb (state_eq (cube v) init_state)
                   (Nat.eqb (length (solution v)) 0)
           then Ret (0, u, bump) else Ret (0, u, k1)
    | 5 =>
        match c_shot cfg with
        | None => Ret (28, u, k1)
        | Some path =>
            rl_screenshot path ;;
            saved <- rl_file_exists path ;;
            Ret (28, u, Script (k_stage k) (S (k_frames k)) saved)
        end
    | _ => Ret (28, u, k1)
    end
  end.

(** * Cube commands

    Every command that can change the cube goes through [Viewer.v], so the
    certified move functions are the only way a sticker ever moves. *)

(** Twenty random turns provide a full scramble for the viewer. *)
Fixpoint scramble (n : nat) (v : view) : itree appE view :=
  match n with
  | 0 => Ret v
  | S k => m <- rl_random 0 17 ;; scramble k (turn_view (code_move m) v)
  end.

(** Replace transient status while leaving the cube and undo history intact. *)
Definition with_status (n : ui_state) (v : view) : view :=
  View (cube v) (history v) [] false n.

(** Abandon a search, if one is running. *)
Definition drop (j : option search) : itree appE unit :=
  match j with Some h => job_cancel h | None => Ret tt end.

(** Process one command, keeping every cube mutation in certified code. *)
Definition command (key : nat) (v : view) (j : option search)
  : itree appE (view * option search) :=
  if Nat.eqb key 20 then drop j ;; Ret (initial_view tt, None)
  else if Nat.eqb key 27 then drop j ;; Ret (with_status Ready v, None)
  else if searching v then Ret (v, j)
  else if andb (Nat.leb 1 key) (Nat.leb key 18) then
    Ret (turn_view (code_move (key - 1)) v, j)
  else
    match key with
    | 19 => scrambled <- scramble 20 (initial_view tt) ;; Ret (scrambled, j)
    | 21 => drop j ;;
            h <- job_start solve_request (colors_of (cube v)) ;;
            Ret (with_status Searching v, Some h)
    | 22 => Ret (step_view v, j)
    | 23 => Ret (View (cube v) (history v) (solution v)
                      (negb (playing v)) (status v), j)
    | 24 => Ret (undo_view v, j)
    | 29 => Ret ((if playing v then step_view v else v), j)
    | _ => Ret (v, j)
    end.

(** Consume the running search's result, validating it before display. *)
Definition receive (v : view) (j : option search) : itree appE view :=
  match j with
  | Some h =>
      if searching v then
        reply <- job_poll h ;;
        match reply with
        | None => Ret v
        | Some None => Ret (with_status NoSolution v)
        | Some (Some moves) => Ret (accept_solution moves v)
        end
      else Ret v
  | None => Ret v
  end.

(** * The frame loop *)

(** A turn in flight owns the cube, so commands cannot pile up behind it. *)
Definition gated (a : app) (u : ui) (now : R) : itree appE (nat * ui) :=
  match s_anim (a_shown a) with
  | Some _ => Ret (0, u)
  | None => read_command a u now
  end.

(** Read one command from the user or from the script. *)
Definition step_input (cfg : config) (a : app) (now : R)
  : itree appE (nat * ui * script) :=
  match c_shot cfg with
  | Some _ => script_command cfg a now
  | None =>
      u <- read_orbit (a_ui a) ;;
      r <- gated a u now ;;
      let '(key, u') := r in Ret (key, u', a_script a)
  end.

(** Shut the viewer down in reverse order of resource acquisition. A search
    still running is abandoned, not waited for. *)
Definition shutdown (cfg : config) (j : option search) : itree appE unit :=
  drop j ;; rl_unload_target (c_target cfg) ;;
  rl_unload_font (c_semibold cfg) ;; rl_unload_font (c_regular cfg) ;;
  rl_close_window.

(** One frame: read input, advance the cube, present the view, and say whether
    this was the last one. Kept separate from the loop because a browser drives
    the loop itself, calling back once per animation frame. *)
Definition step_frame (cfg : config) (a : app) : itree appE (bool * app) :=
  quit <- rl_should_close ;;
  if quit : bool then Ret (true, a)
  else
    now <- rl_time ;;
    r <- step_input cfg a now ;;
    let '(key, u, k) := r in
    if Nat.eqb key 28
    then Ret (true, Mk (a_view a) (a_job a) u (a_shown a) k)
    else
      answered <- command key (a_view a) (a_job a) ;;
      let '(next, j) := answered in
      ready <- receive next j ;;
      let a' := Mk ready j u (advance (a_shown a) ready now) k in
      draw cfg a' now ;;
      Ret (false, a').

(** Each guarded frame steps once, until a frame says it was the last. *)
CoFixpoint frames (cfg : config) (a : app) : itree appE bool :=
  r <- step_frame cfg a ;;
  let '(stop, a') := r in
  if stop : bool
  then shutdown cfg (a_job a') ;; Ret (k_ok (a_script a'))
  else Tau (frames cfg a').

(** Start solved, with nothing on screen yet and the script at its first step. *)
Definition initial_app (shot : option PrimString.string) : app :=
  Mk (initial_view tt) None (Ui home_orbit false 0 0) (Shown [] [] None)
     (Script 0 0 (match shot with None => true | Some _ => false end)).

(** Open the window, load the fonts, and allocate the 3D target. Separate from
    the loop so that a host which owns its own loop can still start us. *)
Definition setup (scale : nat) (shot : option PrimString.string)
  : itree appE (config * app) :=
  rl_init_window "Rubik - a certified cube solver"
    (window_w * scale) (window_h * scale) ;;
  rl_mouse_scale (1 / INR scale) (1 / INR scale) ;;
  regular <- rl_load_font "assets/fonts/IBMPlexSans-Regular.ttf" 64 ;;
  semibold <- rl_load_font "assets/fonts/IBMPlexSans-SemiBold.ttf" 64 ;;
  target <- rl_load_target (canvas_w * scale) (canvas_h * scale) ;;
  Ret (Config target regular semibold shot scale, initial_app shot).

(** Set up, then run until the user quits. The frame rate is capped here and
    not in [setup], because a browser paces its own loop and asking raylib to
    wait there would block the page. *)
Definition program (shot : option PrimString.string) : itree appE bool :=
  started <- setup 1 shot ;;
  let '(cfg, a) := started in
  rl_set_target_fps 60 ;;
  frames cfg a.

(** * Entry point

    The program the host starts. Naming it [main] is what makes extraction
    emit the C++ entry point, so there is no hand-written [main] to keep in
    step with this one.

    Setting [RUBIK_SMOKE] to a path runs the scripted self-test instead of
    reading the keyboard, and writes its screenshot there. Extraction gives
    [main] no arguments, so the choice arrives through the environment. *)
Definition main : itree appE unit :=
  shot <- proc_getenv "RUBIK_SMOKE" ;;
  ok <- program shot ;;
  proc_exit (if ok then 0 else 1).
