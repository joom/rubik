From Stdlib Require Import List Lia PArith Permutation.
From Rubik Require Export Cube.Cubie Cube.Subgroup Cube.Invariant Search.Admissible.
Import ListNotations.

(** * Coordinate tables

    Kociemba's solver never searches over whole cubes. It searches over a few
    projections of one, each small enough to tabulate, and prunes with the
    distance from each projection to its goal.

    Storage, the breadth-first builder, the coordinates and the six tables all
    live together here, and have to. Extraction emits one struct per file and
    does not order those structs by dependency, so a table constant whose
    initialiser reaches into another file's struct does not compile. *)

(** * Storage

    Tables are read in the innermost loop of the search, so they are kept in a
    binary trie on the bits of the index. Indices are binary numerals, which
    serves both ends of the development: a lookup is a walk down the
    constructors rather than arithmetic, which is what lets the kernel run the
    consistency checks below in seconds, and [native/Extract.v] maps the
    numerals to a machine integer, so a fresh index still costs nothing to
    build at every node of the search.

    An index the builder never wrote reads as zero, which is the safe
    direction: a heuristic of zero prunes nothing but never prunes away a
    solution. *)

Inductive trie : Type := Tip | Bin (v : option nat) (l r : trie).

(** A distance table. Reading it is the only thing the search does to decide
    whether a branch is worth entering. *)
Definition table : Type := trie.

(** A table that promises nothing anywhere. *)
Definition empty_table : table := Tip.

(** Follow the index bit by bit, least significant first, one trie level per
    bit. Binary indices make this pattern matching rather than arithmetic, so
    a lookup costs one step per bit both here and in the extracted program. *)
Fixpoint table_find (t : table) (i : positive) : option nat :=
  match t with
  | Tip => None
  | Bin v l r =>
      match i with
      | xH => v
      | xO j => table_find l j
      | xI j => table_find r j
      end
  end.

(** How far this index still has to go. An index the builder never wrote
    reads as zero, which prunes nothing. *)
Definition table_get (t : table) (i : positive) : nat :=
  match table_find t i with Some d => d | None => 0 end.

(** Whether the builder has already recorded a distance here. *)
Definition table_mem (t : table) (i : positive) : bool :=
  match table_find t i with Some _ => true | None => false end.

(** Recording a distance, growing the trie along the index's bits. *)
Fixpoint table_set (t : table) (i : positive) (d : nat) : table :=
  let '(v, l, r) := match t with
                    | Tip => (@None nat, Tip, Tip)
                    | Bin v l r => (v, l, r)
                    end in
  match i with
  | xH => Bin (Some d) l r
  | xO j => Bin v (table_set l j d) r
  | xI j => Bin v l (table_set r j d)
  end.

(** An index is a tuple's entries laid end to end as bit fields, the head of
    the list in the low bits. A coordinate supplies only the field one entry
    occupies. The numeral is built one constructor at a time: multiplying and
    adding instead would run the standard library's binary arithmetic at every
    node of the search, which profiling showed to cost more than everything
    else put together. *)
Fixpoint digits {A : Type} (bits : A -> positive -> positive) (l : list A)
    : positive :=
  match l with [] => xH | x :: r => bits x (digits bits r) end.

(** * Building a table

    Breadth-first search outward from the goals, recording the level at which
    each index is first reached.  Nothing about this is proved: whatever it
    produces is handed to [consistentb] before it is trusted. *)

Definition visit {A : Type} (key : A -> positive) (d : nat)
    (acc : table * list A) (y : A) : table * list A :=
  let (t, seen) := acc in
  if table_mem t (key y) then (t, seen) else (table_set t (key y) d, y :: seen).

(** Expand the frontier one level at a time, recording the level at which
    each index is first reached. *)
Fixpoint sweep {A : Type} (step : A -> list A) (key : A -> positive)
    (fuel d : nat) (t : table) (frontier : list A) : table :=
  match fuel with
  | 0 => t
  | S k =>
      match frontier with
      | [] => t
      | _ =>
          (* Fold each state's own neighbours straight into the accumulator.
             Collecting them all first with [flat_map] would append one large
             list to another at every step. *)
          let (t', next) :=
            fold_left (fun acc x => fold_left (visit key (S d)) (step x) acc)
              frontier (t, []) in
          sweep step key k (S d) t' next
      end
  end.

(** The distance table for a set of goal states. *)
Definition build_table {A : Type} (step : A -> list A) (key : A -> positive)
    (fuel : nat) (goals : list A) : table :=
  sweep step key fuel 0
    (fold_left (fun t g => table_set t (key g) 0) goals empty_table) goals.

(** * What a coordinate is

    The six coordinates below are each the same eight things, spelled out six
    times rather than abstracted behind a record. That is deliberate: the six
    tables are constants the extracted search reads, and a table reached
    through a projection would be rebuilt at every node of the search rather
    than once at start-up. What every one of them supplies is

    - [X_move], how a single turn acts on the projection alone, with a theorem
      proving it agrees with turning the whole cube — that theorem is what
      makes the projection a search space in its own right;
    - [X_step], the states one allowed move away, and [X_goal], the projection
      being where its phase wants it;
    - [X_dom], the whole space, and [X_dom_closed], that stepping cannot leave
      it, always by [tuples_closed] or [perms_closed];
    - [X_bits] and [X_key], the index, laid out by [digits];
    - [X_table] and [X_estimate], the distances the builder found;
    - [X_index] and [X_index_key], the same index read straight off a cube's
      slots, so the search never builds the tuple it is indexing.

    Two lemmas then close the loop for each: [X_checked], which the kernel
    runs, and [X_safe], which turns passing that check into admissibility. *)

(** All eighteen moves, written out rather than taken from [BasicRubik]. The
    tables below are constants whose initialisers run these steps; reaching
    into another module's constant there means reading it before it is built,
    which silently yields an empty table and a heuristic of zero. *)
Definition table_moves : list move :=
  [(Up, CW); (Up, Half); (Up, CCW); (Right, CW); (Right, Half); (Right, CCW);
   (Front, CW); (Front, Half); (Front, CCW); (Down, CW); (Down, Half);
   (Down, CCW); (Left, CW); (Left, Half); (Left, CCW); (Back, CW);
   (Back, Half); (Back, CCW)].

(** The literal really is every move, so a typo in it could not go
    unnoticed. *)
Lemma table_moves_all : table_moves = all_moves.
Proof. reflexivity. Qed.

(** * The corner-orientation coordinate

    The first phase has to bring every corner square with its slot. How far
    each corner is turned is all that matters, and a turn changes those
    rotations without consulting anything else, so the eight rotations form a
    search space of their own with 6561 states. *)

(** Comparing rotations, so a tuple of them has decidable equality. *)
Definition twist_eq_dec (x y : twist) : {x = y} + {x <> y}.
Proof. decide equality. Defined.

(** Every rotation appears in this list. *)
Definition all_twists : list twist := [T0; T1; T2].

(** The three rotations are all of them. *)
Lemma all_twists_complete t : In t all_twists.
Proof. destruct t; simpl; tauto. Qed.

(** A cube with the given rotations and every piece at home. The permutation
    is irrelevant to how the rotations move, so any choice will do. *)
Definition embed_twists (l : list twist) : cube :=
  match l with
  | [a; b; c; d; e; f; g; h] =>
      Cube (URF, a) (UFL, b) (ULB, c) (UBR, d)
           (DFR, e) (DLF, f) (DBL, g) (DRB, h)
           (UR, F0) (UF, F0) (UL, F0) (UB, F0) (DR, F0) (DF, F0)
           (DL, F0) (DB, F0) (FR, F0) (FL, F0) (BL, F0) (BR, F0)
  | _ => solved_cube
  end.

(** How one move acts on the rotations alone. *)
Definition twist_move (m : move) (l : list twist) : list twist :=
  twists (turn_cube m (embed_twists l)).

(** The rotations really are a search space in their own right: a move changes
    them the same way whatever else the cube is doing. *)
Theorem twists_turn_cube m c : twists (turn_cube m c) = twist_move m (twists c).
Proof.
  unfold twist_move; destruct_cube c; destruct m as [f a]; destruct f, a;
    unfold twists, embed_twists; cbn [corner_slots turn_cube quarter_cube
      xURF xUFL xULB xUBR xDFR xDLF xDBL xDRB map]; reflexivity.
Qed.

(** The eighteen rotation tuples one move away. *)
Definition twist_step (l : list twist) : list (list twist) :=
  map (fun m => twist_move m l) table_moves.

(** The first phase is done with the corners when none of them is turned. *)
Definition twist_goal (l : list twist) : bool :=
  if list_eq_dec twist_eq_dec l (repeat T0 8) then true else false.

(** The whole space of eight rotations. *)
Definition twist_dom : list (list twist) := tuples 8 all_twists.

(** Rotations stay eight in number, so stepping never leaves the space. *)
Lemma twist_move_length m l : length l = 8 -> length (twist_move m l) = 8.
Proof.
  intro H; unfold twist_move, twists, corner_slots; rewrite length_map; reflexivity.
Qed.

(** A turn keeps the rotations eight in number, so stepping stays inside the
    space. *)
Lemma twist_dom_closed x y :
  In x twist_dom -> In y (twist_step x) -> In y twist_dom.
Proof.
  apply (tuples_closed all_twists 8 table_moves twist_move);
    [apply all_twists_complete |].
  intros m l Hl; apply twist_move_length, (tuples_length _ _ _ Hl).
Qed.

(** Two bits per corner. *)
Definition twist_bits (t : twist) (k : positive) : positive :=
  match t with
  | T0 => xO (xO (k)) | T1 => xI (xO (k)) | T2 => xO (xI (k))
  end.

(** The eight rotations read as a numeral. *)
Definition twist_key : list twist -> positive := digits twist_bits.

(** The distance table, built by breadth-first search outward from the solved
    rotations. How it was built is not part of any proof. *)
Definition twist_table : table := build_table twist_step twist_key 30 [repeat T0 8].

(** The heuristic it defines: how far the corner rotations still have to go. *)
Definition twist_estimate (l : list twist) : nat :=
  table_get twist_table (twist_key l).

(** The index of a cube's rotations, read straight off its slots. Going via
    [twists] would allocate a list at every node of the search. *)
Definition twist_index (c : cube) : positive :=
  twist_bits (snd (xURF c)) (twist_bits (snd (xUFL c)) (twist_bits (snd (xULB c))
    (twist_bits (snd (xUBR c)) (twist_bits (snd (xDFR c)) (twist_bits (snd (xDLF c))
      (twist_bits (snd (xDBL c)) (twist_bits (snd (xDRB c)) xH))))))).

(** The index read off a cube is the index of that cube's rotations. *)
Lemma twist_index_key c : twist_index c = twist_key (twists c).
Proof. destruct c; reflexivity. Qed.

(** The check itself: a few hundred thousand table readings, which the
    kernel runs in well under a second rather than taking on trust. *)
Lemma twist_checked : consistentb twist_step twist_goal twist_dom twist_estimate = true.
Proof. vm_compute; reflexivity. Qed.

(** Passing it makes the corner-rotation heuristic safe to prune with: it
    never overestimates, so pruning cannot lose a solution. *)
Theorem twist_safe : admissible_on twist_step twist_goal twist_dom twist_estimate.
Proof.
  apply consistentb_admissible; [apply twist_dom_closed | apply twist_checked].
Qed.

(** * The edge-orientation coordinate

    The same story for the twelve edges: a turn flips edges without consulting
    anything else, so the flips form a space of 4096 states. *)

Definition flip_eq_dec (x y : flip) : {x = y} + {x <> y}.
Proof. decide equality. Defined.

(** Both flips. *)
Definition all_flips : list flip := [F0; F1].

(** And they are all of them. *)
Lemma all_flips_complete f : In f all_flips.
Proof. destruct f; simpl; tauto. Qed.

(** A cube with the given flips and every piece at home. *)
Definition embed_flips (l : list flip) : cube :=
  match l with
  | [a; b; c; d; e; f; g; h; i; j; k; n] =>
      Cube (URF, T0) (UFL, T0) (ULB, T0) (UBR, T0)
           (DFR, T0) (DLF, T0) (DBL, T0) (DRB, T0)
           (UR, a) (UF, b) (UL, c) (UB, d) (DR, e) (DF, f)
           (DL, g) (DB, h) (FR, i) (FL, j) (BL, k) (BR, n)
  | _ => solved_cube
  end.

(** How one move acts on the flips alone. *)
Definition flip_move (m : move) (l : list flip) : list flip :=
  flips (turn_cube m (embed_flips l)).

(** The flips move the same way whatever else the cube is doing. *)
Theorem flips_turn_cube m c : flips (turn_cube m c) = flip_move m (flips c).
Proof.
  unfold flip_move; destruct_cube c; destruct m as [f a]; destruct f, a;
    unfold flips, embed_flips; cbn [edge_slots turn_cube quarter_cube
      yUR yUF yUL yUB yDR yDF yDL yDB yFR yFL yBL yBR map]; reflexivity.
Qed.

(** The eighteen flip tuples one move away. *)
Definition flip_step (l : list flip) : list (list flip) :=
  map (fun m => flip_move m l) table_moves.

(** The first phase is done with the edges when none of them is flipped. *)
Definition flip_goal (l : list flip) : bool :=
  if list_eq_dec flip_eq_dec l (repeat F0 12) then true else false.

(** The whole space of twelve flips. *)
Definition flip_dom : list (list flip) := tuples 12 all_flips.

(** A turn keeps the flips twelve in number. *)
Lemma flip_move_length m l : length (flip_move m l) = 12.
Proof. unfold flip_move, flips, edge_slots; rewrite length_map; reflexivity. Qed.

(** So stepping stays inside the space. *)
Lemma flip_dom_closed x y :
  In x flip_dom -> In y (flip_step x) -> In y flip_dom.
Proof.
  apply (tuples_closed all_flips 12 table_moves flip_move);
    [apply all_flips_complete | intros m l _; apply flip_move_length].
Qed.

(** One bit per edge. *)
Definition flip_bit (f : flip) (k : positive) : positive :=
  match f with F0 => xO k | F1 => xI k end.

(** The flips read as a numeral. *)
Definition flip_key : list flip -> positive := digits flip_bit.

(** Distances to the unflipped state, built by breadth-first search. *)
Definition flip_table : table := build_table flip_step flip_key 30 [repeat F0 12].

(** How far the edge flips still have to go. *)
Definition flip_estimate (l : list flip) : nat :=
  table_get flip_table (flip_key l).

(** The same for the flips and for the slice occupancy. *)
Definition flip_index (c : cube) : positive :=
  flip_bit (snd (yUR c)) (flip_bit (snd (yUF c)) (flip_bit (snd (yUL c))
    (flip_bit (snd (yUB c)) (flip_bit (snd (yDR c)) (flip_bit (snd (yDF c))
      (flip_bit (snd (yDL c)) (flip_bit (snd (yDB c)) (flip_bit (snd (yFR c))
        (flip_bit (snd (yFL c)) (flip_bit (snd (yBL c))
          (flip_bit (snd (yBR c)) xH))))))))))).

(** The index read off a cube is the index of that cube's flips. *)
Lemma flip_index_key c : flip_index c = flip_key (flips c).
Proof. destruct c; reflexivity. Qed.

(** The same check for the edge flips. *)
Lemma flip_checked : consistentb flip_step flip_goal flip_dom flip_estimate = true.
Proof. vm_compute; reflexivity. Qed.

(** Passing it makes the edge-flip heuristic safe to prune with: it
    never overestimates, so pruning cannot lose a solution. *)
Theorem flip_safe : admissible_on flip_step flip_goal flip_dom flip_estimate.
Proof.
  apply consistentb_admissible; [apply flip_dom_closed | apply flip_checked].
Qed.

(** * The slice coordinate

    The last thing the first phase must arrange is that the four slice edges
    are back in the slice, in any order. Only which slots hold them matters. *)

(** A slice edge where the mask says so, and some other edge where it does not. *)
Definition slice_piece (b : bool) : edge := if b then FR else UR.

(** A cube whose slice edges sit exactly where the mask says. Pieces may
    repeat, which no scramble would produce, but the mask is all that is read
    and a turn moves it the same way regardless. *)
Definition embed_slice (l : list bool) : cube :=
  match l with
  | [a; b; c; d; e; f; g; h; i; j; k; n] =>
      Cube (URF, T0) (UFL, T0) (ULB, T0) (UBR, T0)
           (DFR, T0) (DLF, T0) (DBL, T0) (DRB, T0)
           (slice_piece a, F0) (slice_piece b, F0) (slice_piece c, F0)
           (slice_piece d, F0) (slice_piece e, F0) (slice_piece f, F0)
           (slice_piece g, F0) (slice_piece h, F0) (slice_piece i, F0)
           (slice_piece j, F0) (slice_piece k, F0) (slice_piece n, F0)
  | _ => solved_cube
  end.

(** Reading the mask back off such a cube returns it unchanged. *)
Lemma is_slice_pick (b : bool) : is_slice (slice_piece b) = b.
Proof. destruct b; reflexivity. Qed.

(** How one move acts on the slice occupancy alone. *)
Definition slice_move (m : move) (l : list bool) : list bool :=
  slice_mask (turn_cube m (embed_slice l)).

(** Which slots hold slice edges moves the same way whatever else is going on. *)
Theorem slice_mask_turn_cube m c : slice_mask (turn_cube m c) = slice_move m (slice_mask c).
Proof.
  unfold slice_move; destruct_cube c; destruct m as [f a]; destruct f, a;
    unfold slice_mask, edge_pieces, embed_slice; cbn [edge_slots turn_cube quarter_cube
      yUR yUF yUL yUB yDR yDF yDL yDB yFR yFL yBL yBR map];
    rewrite ?shift_edge_fst; cbn [fst];
    rewrite !is_slice_pick; reflexivity.
Qed.

(** The eighteen occupancy masks one move away. *)
Definition slice_step (l : list bool) : list (list bool) :=
  map (fun m => slice_move m l) table_moves.

(** The first phase is done with the slice when its four edges are back in
    it. *)
Definition slice_goal (l : list bool) : bool :=
  if list_eq_dec Bool.bool_dec l slice_home then true else false.

(** The whole space of twelve-slot masks. *)
Definition slice_dom : list (list bool) := tuples 12 [true; false].

(** A turn keeps the mask twelve slots wide. *)
Lemma slice_move_length m l : length (slice_move m l) = 12.
Proof.
  unfold slice_move, slice_mask, edge_pieces, edge_slots;
    rewrite !length_map; reflexivity.
Qed.

(** So stepping stays inside the space. *)
Lemma slice_dom_closed x y :
  In x slice_dom -> In y (slice_step x) -> In y slice_dom.
Proof.
  apply (tuples_closed [true; false] 12 table_moves slice_move);
    [intros [|]; simpl; tauto | intros m l _; apply slice_move_length].
Qed.

(** One bit per slot, set when the slot holds a slice edge. *)
Definition mask_bit (b : bool) (k : positive) : positive := if b then xI k else xO k.

(** The same bit, read off the edge sitting in the slot rather than off the
    mask, which is how the search indexes a cube without building the mask. *)
Definition slice_bit (e : edge) : positive -> positive := mask_bit (is_slice e).

(** The mask read as a numeral. *)
Definition slice_key : list bool -> positive := digits mask_bit.

(** Distances to the slice being intact. *)
Definition slice_table : table := build_table slice_step slice_key 30 [slice_home].

(** How far the slice edges still have to travel. *)
Definition slice_estimate (l : list bool) : nat :=
  table_get slice_table (slice_key l).

(** The occupancy index read straight off a cube's slots. *)
Definition slice_index (c : cube) : positive :=
  slice_bit (fst (yUR c)) (slice_bit (fst (yUF c)) (slice_bit (fst (yUL c))
    (slice_bit (fst (yUB c)) (slice_bit (fst (yDR c)) (slice_bit (fst (yDF c))
      (slice_bit (fst (yDL c)) (slice_bit (fst (yDB c)) (slice_bit (fst (yFR c))
        (slice_bit (fst (yFL c)) (slice_bit (fst (yBL c))
          (slice_bit (fst (yBR c)) xH))))))))))).

(** And it agrees with the index of that cube's mask. *)
Lemma slice_index_key c : slice_index c = slice_key (slice_mask c).
Proof. destruct c; reflexivity. Qed.

(** And for the slice. *)
Lemma slice_checked : consistentb slice_step slice_goal slice_dom slice_estimate = true.
Proof. vm_compute; reflexivity. Qed.

(** Passing it makes the slice heuristic safe to prune with: it
    never overestimates, so pruning cannot lose a solution. *)
Theorem slice_safe : admissible_on slice_step slice_goal slice_dom slice_estimate.
Proof.
  apply consistentb_admissible; [apply slice_dom_closed | apply slice_checked].
Qed.

(** * The corner-permutation coordinate

    Once the first phase is done, the second has only to put pieces back in
    their slots, and it may use only ten of the eighteen moves. Where the
    eight corners sit is one coordinate of that, with 40320 states. *)

(** Comparing corners, so a tuple of them has decidable equality. *)
Definition corner_eq_dec (x y : corner) : {x = y} + {x <> y}.
Proof. decide equality. Defined.

(** The eight corners in slot order. *)
Definition all_corners : list corner := [URF; UFL; ULB; UBR; DFR; DLF; DBL; DRB].

(** A cube with the corners placed as given and nothing turned. *)
Definition embed_cornerperm (l : list corner) : cube :=
  match l with
  | [a; b; c; d; e; f; g; h] =>
      Cube (a, T0) (b, T0) (c, T0) (d, T0) (e, T0) (f, T0) (g, T0) (h, T0)
           (UR, F0) (UF, F0) (UL, F0) (UB, F0) (DR, F0) (DF, F0)
           (DL, F0) (DB, F0) (FR, F0) (FL, F0) (BL, F0) (BR, F0)
  | _ => solved_cube
  end.

(** How one move rearranges the corners. *)
Definition cornerperm_move (m : move) (l : list corner) : list corner :=
  corner_pieces (turn_cube m (embed_cornerperm l)).

(** Where the corners sit moves the same way whatever else is going on. *)
Theorem corner_pieces_turn_cube m c :
  corner_pieces (turn_cube m c) = cornerperm_move m (corner_pieces c).
Proof.
  unfold cornerperm_move; destruct_cube c; destruct m as [f a]; destruct f, a;
    unfold corner_pieces, embed_cornerperm; cbn [corner_slots turn_cube quarter_cube
      xURF xUFL xULB xUBR xDFR xDLF xDBL xDRB map];
    rewrite ?shift_corner_fst; cbn [fst]; reflexivity.
Qed.

(** The ten placements one allowed move away. *)
Definition cornerperm_step (l : list corner) : list (list corner) :=
  map (fun m => cornerperm_move m l) phase2_moves.

(** The corners are done when each is back in its own slot. *)
Definition cornerperm_goal (l : list corner) : bool :=
  if list_eq_dec corner_eq_dec l all_corners then true else false.

(** Every rearrangement of the eight corners. *)
Definition cornerperm_dom : list (list corner) := perms all_corners.

(** A turn rearranges the eight corners, so it cannot leave the space of
    rearrangements. *)
Lemma cornerperm_move_perm m l :
  In l cornerperm_dom -> Permutation l (cornerperm_move m l).
Proof.
  intro Hl; apply perms_sound in Hl.
  assert (Hlen : length l = 8)
    by (rewrite <- (Permutation_length Hl); reflexivity).
  destruct l as [| a1 [| a2 [| a3 [| a4 [| a5 [| a6 [| a7 [| a8 [| a9 l]]]]]]]]];
    simpl in Hlen; try discriminate.
  destruct m as [f t]; destruct f, t;
    unfold cornerperm_move, corner_pieces, embed_cornerperm;
    cbn [corner_slots turn_cube quarter_cube xURF xUFL xULB xUBR xDFR xDLF xDBL xDRB map];
    rewrite ?shift_corner_fst; cbn [fst];
    permutation_by_count corner_eq_dec.
Qed.

(** A turn rearranges corners, so stepping stays among rearrangements. *)
Lemma cornerperm_dom_closed x y :
  In x cornerperm_dom -> In y (cornerperm_step x) -> In y cornerperm_dom.
Proof.
  apply (perms_closed all_corners phase2_moves cornerperm_move).
  intros m l _ Hl; apply cornerperm_move_perm, Hl.
Qed.

(** Index a placement by reading the slots as a base-eight numeral. The key
    space is larger than the 40320 placements that occur, which costs nothing:
    the table is a radix tree and never stores an index it was not given. *)
Definition corner_bits (x : corner) (k : positive) : positive :=
  match x with
  | URF => xO (xO (xO (k)))
  | UFL => xI (xO (xO (k)))
  | ULB => xO (xI (xO (k)))
  | UBR => xI (xI (xO (k)))
  | DFR => xO (xO (xI (k)))
  | DLF => xI (xO (xI (k)))
  | DBL => xO (xI (xI (k)))
  | DRB => xI (xI (xI (k)))
  end.

(** Three bits per corner: the placement read as a numeral. *)
Definition cornerperm_key : list corner -> positive := digits corner_bits.

(** Distances to the corners being home, under the second phase's moves. *)
Definition cornerperm_table : table :=
  build_table cornerperm_step cornerperm_key 30 [all_corners].

(** How far the corners still have to travel. *)
Definition cornerperm_estimate (l : list corner) : nat :=
  table_get cornerperm_table (cornerperm_key l).

(** The corner placement index read straight off a cube's slots. *)
Definition cornerperm_index (c : cube) : positive :=
  corner_bits (fst (xURF c)) (corner_bits (fst (xUFL c)) (corner_bits (fst (xULB c))
    (corner_bits (fst (xUBR c)) (corner_bits (fst (xDFR c)) (corner_bits (fst (xDLF c))
      (corner_bits (fst (xDBL c)) (corner_bits (fst (xDRB c)) xH))))))).

(** And it agrees with the index of that cube's corners. *)
Lemma cornerperm_index_key c : cornerperm_index c = cornerperm_key (corner_pieces c).
Proof. destruct c; reflexivity. Qed.

(** The same again for the corner placements. *)
Lemma cornerperm_checked : consistentb cornerperm_step cornerperm_goal cornerperm_dom cornerperm_estimate = true.
Proof. vm_compute; reflexivity. Qed.

(** Passing it makes the corner-placement heuristic safe to prune with: it
    never overestimates, so pruning cannot lose a solution. *)
Theorem cornerperm_safe : admissible_on cornerperm_step cornerperm_goal cornerperm_dom cornerperm_estimate.
Proof.
  apply consistentb_admissible; [apply cornerperm_dom_closed | apply cornerperm_checked].
Qed.

(** * The edge-placement coordinates

    Inside the subgroup the eight up and down edges stay among their own eight
    slots and the four slice edges stay in the slice, so where each group sits
    is two further coordinates: 40320 states and 24. *)

Definition edge_eq_dec (x y : edge) : {x = y} + {x <> y}.
Proof. decide equality. Defined.

(** The eight edges that never enter the slice. *)
Definition ud_edges : list edge := [UR; UF; UL; UB; DR; DF; DL; DB].
(** And the four that live in it. *)
Definition slice_edges : list edge := [FR; FL; BL; BR].

(** A cube with the non-slice edges placed as given. *)
Definition embed_udperm (l : list edge) : cube :=
  match l with
  | [a; b; c; d; e; f; g; h] =>
      Cube (URF, T0) (UFL, T0) (ULB, T0) (UBR, T0)
           (DFR, T0) (DLF, T0) (DBL, T0) (DRB, T0)
           (a, F0) (b, F0) (c, F0) (d, F0) (e, F0) (f, F0) (g, F0) (h, F0)
           (FR, F0) (FL, F0) (BL, F0) (BR, F0)
  | _ => solved_cube
  end.

(** A cube with the slice edges placed as given. *)
Definition embed_sliceperm (l : list edge) : cube :=
  match l with
  | [a; b; c; d] =>
      Cube (URF, T0) (UFL, T0) (ULB, T0) (UBR, T0)
           (DFR, T0) (DLF, T0) (DBL, T0) (DRB, T0)
           (UR, F0) (UF, F0) (UL, F0) (UB, F0) (DR, F0) (DF, F0)
           (DL, F0) (DB, F0) (a, F0) (b, F0) (c, F0) (d, F0)
  | _ => solved_cube
  end.

(** How one allowed move rearranges the non-slice edges. *)
Definition udperm_move (m : move) (l : list edge) : list edge :=
  ud_pieces (turn_cube m (embed_udperm l)).

(** And the slice edges. *)
Definition sliceperm_move (m : move) (l : list edge) : list edge :=
  slice_pieces (turn_cube m (embed_sliceperm l)).

(** Both groups move on their own, so long as the move is one the second phase
    is allowed: those are exactly the moves that keep the groups apart. *)
Theorem ud_pieces_turn_cube m c :
  phase2_move m = true -> ud_pieces (turn_cube m c) = udperm_move m (ud_pieces c).
Proof.
  destruct m as [f a]; destruct f, a; try discriminate; intros _;
    unfold udperm_move; destruct_cube c;
    unfold ud_pieces, edge_pieces, embed_udperm; cbn [edge_slots turn_cube quarter_cube
      yUR yUF yUL yUB yDR yDF yDL yDB yFR yFL yBL yBR map firstn];
    rewrite ?shift_edge_fst; cbn [fst]; reflexivity.
Qed.

(** The slice edges move on their own too, for the same reason. *)
Theorem slice_pieces_turn_cube m c :
  phase2_move m = true -> slice_pieces (turn_cube m c) = sliceperm_move m (slice_pieces c).
Proof.
  destruct m as [f a]; destruct f, a; try discriminate; intros _;
    unfold sliceperm_move; destruct_cube c;
    unfold slice_pieces, edge_pieces, embed_sliceperm; cbn [edge_slots turn_cube quarter_cube
      yUR yUF yUL yUB yDR yDF yDL yDB yFR yFL yBL yBR map skipn];
    rewrite ?shift_edge_fst; cbn [fst]; reflexivity.
Qed.

(** The ten placements one allowed move away. *)
Definition udperm_step (l : list edge) : list (list edge) :=
  map (fun m => udperm_move m l) phase2_moves.

(** Likewise for the slice. *)
Definition sliceperm_step (l : list edge) : list (list edge) :=
  map (fun m => sliceperm_move m l) phase2_moves.

(** The non-slice edges are done when each is back in its own slot. *)
Definition udperm_goal (l : list edge) : bool :=
  if list_eq_dec edge_eq_dec l ud_edges then true else false.

(** Likewise for the slice edges. *)
Definition sliceperm_goal (l : list edge) : bool :=
  if list_eq_dec edge_eq_dec l slice_edges then true else false.

(** Every rearrangement of the eight non-slice edges. *)
Definition udperm_dom : list (list edge) := perms ud_edges.
(** And of the four slice edges. *)
Definition sliceperm_dom : list (list edge) := perms slice_edges.

(** An allowed move rearranges the eight without letting any escape. *)
Lemma udperm_move_perm m l :
  phase2_move m = true -> In l udperm_dom -> Permutation l (udperm_move m l).
Proof.
  intros Hm Hl; apply perms_sound in Hl.
  assert (Hlen : length l = 8)
    by (rewrite <- (Permutation_length Hl); reflexivity).
  destruct l as [| a1 [| a2 [| a3 [| a4 [| a5 [| a6 [| a7 [| a8 [| a9 l]]]]]]]]];
    simpl in Hlen; try discriminate.
  destruct m as [f t]; destruct f, t; try discriminate;
    unfold udperm_move, ud_pieces, edge_pieces, embed_udperm;
    cbn [edge_slots turn_cube quarter_cube yUR yUF yUL yUB yDR yDF yDL yDB
         yFR yFL yBL yBR map firstn];
    rewrite ?shift_edge_fst; cbn [fst];
    permutation_by_count edge_eq_dec.
Qed.

(** And rearranges the four within the slice. *)
Lemma sliceperm_move_perm m l :
  phase2_move m = true -> In l sliceperm_dom -> Permutation l (sliceperm_move m l).
Proof.
  intros Hm Hl; apply perms_sound in Hl.
  assert (Hlen : length l = 4)
    by (rewrite <- (Permutation_length Hl); reflexivity).
  destruct l as [| a1 [| a2 [| a3 [| a4 [| a5 l]]]]]; simpl in Hlen; try discriminate.
  destruct m as [f t]; destruct f, t; try discriminate;
    unfold sliceperm_move, slice_pieces, edge_pieces, embed_sliceperm;
    cbn [edge_slots turn_cube quarter_cube yUR yUF yUL yUB yDR yDF yDL yDB
         yFR yFL yBL yBR map skipn];
    rewrite ?shift_edge_fst; cbn [fst];
    permutation_by_count edge_eq_dec.
Qed.

(** So stepping stays among rearrangements. *)
Lemma udperm_dom_closed x y :
  In x udperm_dom -> In y (udperm_step x) -> In y udperm_dom.
Proof.
  apply (perms_closed ud_edges phase2_moves udperm_move).
  intros m l Hm Hl; apply udperm_move_perm; auto using phase2_moves_allowed.
Qed.

(** Likewise for the slice. *)
Lemma sliceperm_dom_closed x y :
  In x sliceperm_dom -> In y (sliceperm_step x) -> In y sliceperm_dom.
Proof.
  apply (perms_closed slice_edges phase2_moves sliceperm_move).
  intros m l Hm Hl; apply sliceperm_move_perm; auto using phase2_moves_allowed.
Qed.

(** Four bits per edge. *)
Definition edge_bits (x : edge) (k : positive) : positive :=
  match x with
  | UR => xO (xO (xO (xO (k))))
  | UF => xI (xO (xO (xO (k))))
  | UL => xO (xI (xO (xO (k))))
  | UB => xI (xI (xO (xO (k))))
  | DR => xO (xO (xI (xO (k))))
  | DF => xI (xO (xI (xO (k))))
  | DL => xO (xI (xI (xO (k))))
  | DB => xI (xI (xI (xO (k))))
  | FR => xO (xO (xO (xI (k))))
  | FL => xI (xO (xO (xI (k))))
  | BL => xO (xI (xO (xI (k))))
  | BR => xI (xI (xO (xI (k))))
  end.

(** A tuple of edges read as a numeral. *)
Definition edge_key : list edge -> positive := digits edge_bits.

(** Indexing the non-slice placement. *)
Definition udperm_key (l : list edge) : positive := edge_key l.
(** And the slice placement. *)
Definition sliceperm_key (l : list edge) : positive := edge_key l.

(** Distances to the non-slice edges being home. *)
Definition udperm_table : table := build_table udperm_step udperm_key 30 [ud_edges].
(** And to the slice edges being home. *)
Definition sliceperm_table : table :=
  build_table sliceperm_step sliceperm_key 30 [slice_edges].

(** The placement indices read straight off a cube's slots. *)
Definition udperm_index (c : cube) : positive :=
  edge_bits (fst (yUR c)) (edge_bits (fst (yUF c)) (edge_bits (fst (yUL c))
    (edge_bits (fst (yUB c)) (edge_bits (fst (yDR c)) (edge_bits (fst (yDF c))
      (edge_bits (fst (yDL c)) (edge_bits (fst (yDB c)) xH))))))).

(** The slice placement index, likewise. *)
Definition sliceperm_index (c : cube) : positive :=
  edge_bits (fst (yFR c)) (edge_bits (fst (yFL c)) (edge_bits (fst (yBL c))
    (edge_bits (fst (yBR c)) xH))).

(** Both agree with the indices of the cube's own edge tuples. *)
Lemma udperm_index_key c : udperm_index c = udperm_key (ud_pieces c).
Proof. destruct c; reflexivity. Qed.

(** Likewise for the slice. *)
Lemma sliceperm_index_key c : sliceperm_index c = sliceperm_key (slice_pieces c).
Proof. destruct c; reflexivity. Qed.

(** How far the non-slice edges still have to travel. *)
Definition udperm_estimate (l : list edge) : nat :=
  table_get udperm_table (udperm_key l).
(** And the slice edges. *)
Definition sliceperm_estimate (l : list edge) : nat :=
  table_get sliceperm_table (sliceperm_key l).

(** For the outer edges, *)
Lemma udperm_checked : consistentb udperm_step udperm_goal udperm_dom udperm_estimate = true.
Proof. vm_compute; reflexivity. Qed.

(** Passing it makes the outer-edge heuristic safe to prune with: it
    never overestimates, so pruning cannot lose a solution. *)
Theorem udperm_safe : admissible_on udperm_step udperm_goal udperm_dom udperm_estimate.
Proof.
  apply consistentb_admissible; [apply udperm_dom_closed | apply udperm_checked].
Qed.

(** and for the slice edges. *)
Lemma sliceperm_checked : consistentb sliceperm_step sliceperm_goal sliceperm_dom sliceperm_estimate = true.
Proof. vm_compute; reflexivity. Qed.

(** Passing it makes the slice-placement heuristic safe to prune with: it
    never overestimates, so pruning cannot lose a solution. *)
Theorem sliceperm_safe : admissible_on sliceperm_step sliceperm_goal sliceperm_dom sliceperm_estimate.
Proof.
  apply consistentb_admissible; [apply sliceperm_dom_closed | apply sliceperm_checked].
Qed.
