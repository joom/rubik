From Stdlib Require Import List Lia PArith NArith Permutation FMapPositive.
From Rubik Require Export Cubie Subgroup Invariant Admissible.
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
    binary trie on the bits of the index.  The index is a plain number: an
    earlier version indexed by [positive] and profiling showed the search
    spending most of its time allocating and freeing those, since a fresh one
    is built at every node.  A number extracts to a machine integer and costs
    nothing to compute.

    An index the builder never wrote reads as zero, which is the safe
    direction: a heuristic of zero prunes nothing but never prunes away a
    solution. *)

Inductive trie : Type := Tip | Bin (v : option nat) (l r : trie).

(** A distance table. Reading it is the only thing the search does to decide
    whether a branch is worth entering. *)
Definition table : Type := trie.

(** A table that promises nothing anywhere. *)
Definition empty_table : table := Tip.

(** Walk the bits of the index, least significant first, stopping when the
    remaining index is zero.  The walk recurses on the trie, so it terminates
    whatever the index is. *)
Fixpoint tfind (t : table) (i : nat) : option nat :=
  match t with
  | Tip => None
  | Bin v l r =>
      if Nat.eqb i 0 then v
      else if Nat.eqb (Nat.modulo i 2) 0
           then tfind l (Nat.div i 2)
           else tfind r (Nat.div i 2)
  end.

(** How far this index still has to go. An index the builder never wrote
    reads as zero, which prunes nothing. *)
Definition tget (t : table) (i : nat) : nat :=
  match tfind t i with Some d => d | None => 0 end.

(** Whether the builder has already recorded a distance here. *)
Definition tmem (t : table) (i : nat) : bool :=
  match tfind t i with Some _ => true | None => false end.

(** Writing recurses on the index rather than the trie, so it is given a fuel.
    Sixty-four bits is more than any index here needs, and writing happens only
    while a table is being built. *)
Fixpoint tset_aux (fuel : nat) (t : table) (i d : nat) : table :=
  match fuel with
  | 0 => t
  | S k =>
      let '(v, l, r) := match t with
                        | Tip => (@None nat, Tip, Tip)
                        | Bin v l r => (v, l, r)
                        end in
      if Nat.eqb i 0 then Bin (Some d) l r
      else if Nat.eqb (Nat.modulo i 2) 0
           then Bin v (tset_aux k l (Nat.div i 2) d) r
           else Bin v l (tset_aux k r (Nat.div i 2) d)
  end.

(** Record a distance, giving the write enough fuel for any index that
    occurs here. *)
Definition tset (t : table) (i d : nat) : table := tset_aux 64 t i d.

(** * Building a table

    Breadth-first search outward from the goals, recording the level at which
    each index is first reached.  Nothing about this is proved: whatever it
    produces is handed to [consistentb] before it is trusted. *)

Definition visit {A : Type} (key : A -> nat) (d : nat)
    (acc : table * list A) (y : A) : table * list A :=
  let (t, seen) := acc in
  if tmem t (key y) then (t, seen) else (tset t (key y) d, y :: seen).

(** Expand the frontier one level at a time, recording the level at which
    each index is first reached. *)
Fixpoint sweep {A : Type} (step : A -> list A) (key : A -> nat)
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
Definition build {A : Type} (step : A -> list A) (key : A -> nat)
    (fuel : nat) (goals : list A) : table :=
  sweep step key fuel 0
    (fold_left (fun t g => tset t (key g) 0) goals empty_table) goals.

(** * The corner-orientation coordinate

    The first phase has to bring every corner square with its slot. How far
    each corner is turned is all that matters, and a turn changes those
    rotations without consulting anything else, so the eight rotations form a
    search space of their own with 6561 states. *)

(** All eighteen moves, written out rather than taken from [BasicRubik]. The
    tables below are constants whose initialisers run these steps; reaching
    into another module's constant there means reading it before it is built,
    which silently yields an empty table and a heuristic of zero. *)
Definition Movel1 : list move :=
  [(Up, CW); (Up, Half); (Up, CCW); (Right, CW); (Right, Half); (Right, CCW);
   (Front, CW); (Front, Half); (Front, CCW); (Down, CW); (Down, Half);
   (Down, CCW); (Left, CW); (Left, Half); (Left, CCW); (Back, CW);
   (Back, Half); (Back, CCW)].

(** The literal really is every move, so a typo in it could not go
    unnoticed. *)
Lemma Movel1_Movel : Movel1 = Movel.
Proof. reflexivity. Qed.

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
  | _ => csolved
  end.

(** How one move acts on the rotations alone. *)
Definition twist_move (m : move) (l : list twist) : list twist :=
  twists (cm2f m (embed_twists l)).

(** The rotations really are a search space in their own right: a move changes
    them the same way whatever else the cube is doing. *)
Theorem twists_cm2f m c : twists (cm2f m c) = twist_move m (twists c).
Proof.
  unfold twist_move; destruct_cube c; destruct m as [f a]; destruct f, a;
    unfold twists, embed_twists; cbn [cslots cm2f cquarter
      xURF xUFL xULB xUBR xDFR xDLF xDBL xDRB map]; reflexivity.
Qed.

(** The eighteen rotation tuples one move away. *)
Definition twist_step (l : list twist) : list (list twist) :=
  map (fun m => twist_move m l) Movel1.

(** The first phase is done with the corners when none of them is turned. *)
Definition twist_goal (l : list twist) : bool :=
  if list_eq_dec twist_eq_dec l (repeat T0 8) then true else false.

(** The whole space of eight rotations. *)
Definition twist_dom : list (list twist) := tuples 8 all_twists.

(** Rotations stay eight in number, so stepping never leaves the space. *)
Lemma twist_move_length m l : length l = 8 -> length (twist_move m l) = 8.
Proof.
  intro H; unfold twist_move, twists, cslots; rewrite length_map; reflexivity.
Qed.

(** A turn keeps the rotations eight in number, so stepping stays inside the
    space. *)
Lemma twist_dom_closed x y :
  In x twist_dom -> In y (twist_step x) -> In y twist_dom.
Proof.
  intros Hx Hy; apply tuples_length in Hx.
  apply in_map_iff in Hy as [m [<- _]].
  apply tuples_complete; [apply all_twists_complete | apply twist_move_length; auto].
Qed.

(** Index a rotation tuple by reading it as a base-three numeral. The arith-
    metic is binary: an index is computed at every node of the search, and
    counting up to it one unit at a time would cost more than the lookup
    saves. *)
(** Index a tuple by laying its entries end to end as bit fields.  The index
    is built one constructor at a time: computing it by multiplying and adding
    instead runs the standard library's binary arithmetic at every node of the
    search, which profiling showed to cost more than everything else put
    together. *)
Definition twist_bits (t : twist) (k : nat) : nat :=
  match t with T0 => 4 * k | T1 => 1 + 4 * k | T2 => 2 + 4 * k end.

(** Two bits per corner, the head of the list in the low bits. *)
Fixpoint twist_key (l : list twist) : nat :=
  match l with [] => 0 | t :: r => twist_bits t (twist_key r) end.

(** The distance table, built by breadth-first search outward from the solved
    rotations. How it was built is not part of any proof. *)
Definition twist_table : table := build twist_step twist_key 30 [repeat T0 8].

(** The heuristic it defines: how far the corner rotations still have to go. *)
Definition twist_h (l : list twist) : nat := tget twist_table (twist_key l).

(** The index of a cube's rotations, read straight off its slots. Going via
    [twists] would allocate a list at every node of the search. *)
Definition twist_index (c : cube) : nat :=
  twist_bits (snd (xURF c)) (twist_bits (snd (xUFL c)) (twist_bits (snd (xULB c))
    (twist_bits (snd (xUBR c)) (twist_bits (snd (xDFR c)) (twist_bits (snd (xDLF c))
      (twist_bits (snd (xDBL c)) (twist_bits (snd (xDRB c)) 0))))))).

(** The index read off a cube is the index of that cube's rotations. *)
Lemma twist_index_key c : twist_index c = twist_key (twists c).
Proof. destruct c; reflexivity. Qed.

(** Passing the consistency check makes the heuristic safe to prune with.

    The check is left for the program to run at startup rather than being
    discharged here. It is a claim about six thousand table entries, and a
    proof by computation forces the kernel to replay that computation on every
    independent recheck, which costs minutes where running it costs
    milliseconds. The implication is what deserves a proof; the arithmetic
    does not. *)
Theorem twist_h_admissible :
  consistentb twist_step twist_goal twist_dom twist_h = true ->
  admissible_on twist_step twist_goal twist_dom twist_h.
Proof.
  intro H; apply consistentb_admissible; [apply twist_dom_closed | exact H].
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
  | _ => csolved
  end.

(** How one move acts on the flips alone. *)
Definition flip_move (m : move) (l : list flip) : list flip :=
  flips (cm2f m (embed_flips l)).

(** The flips move the same way whatever else the cube is doing. *)
Theorem flips_cm2f m c : flips (cm2f m c) = flip_move m (flips c).
Proof.
  unfold flip_move; destruct_cube c; destruct m as [f a]; destruct f, a;
    unfold flips, embed_flips; cbn [eslots cm2f cquarter
      yUR yUF yUL yUB yDR yDF yDL yDB yFR yFL yBL yBR map]; reflexivity.
Qed.

(** The eighteen flip tuples one move away. *)
Definition flip_step (l : list flip) : list (list flip) :=
  map (fun m => flip_move m l) Movel1.

(** The first phase is done with the edges when none of them is flipped. *)
Definition flip_goal (l : list flip) : bool :=
  if list_eq_dec flip_eq_dec l (repeat F0 12) then true else false.

(** The whole space of twelve flips. *)
Definition flip_dom : list (list flip) := tuples 12 all_flips.

(** A turn keeps the flips twelve in number. *)
Lemma flip_move_length m l : length (flip_move m l) = 12.
Proof. unfold flip_move, flips, eslots; rewrite length_map; reflexivity. Qed.

(** So stepping stays inside the space. *)
Lemma flip_dom_closed x y :
  In x flip_dom -> In y (flip_step x) -> In y flip_dom.
Proof.
  intros _ Hy; apply in_map_iff in Hy as [m [<- _]].
  apply tuples_complete; [apply all_flips_complete | apply flip_move_length].
Qed.

(** One bit per edge. *)
Definition flip_bit (f : flip) (k : nat) : nat :=
  match f with F0 => 2 * k | F1 => 1 + 2 * k end.

(** The flips read as a binary numeral. *)
Fixpoint flip_key (l : list flip) : nat :=
  match l with [] => 0 | f :: r => flip_bit f (flip_key r) end.

(** Distances to the unflipped state, built by breadth-first search. *)
Definition flip_table : table := build flip_step flip_key 30 [repeat F0 12].

(** How far the edge flips still have to go. *)
Definition flip_h (l : list flip) : nat := tget flip_table (flip_key l).

(** The same for the flips and for the slice occupancy. *)
Definition flip_index (c : cube) : nat :=
  flip_bit (snd (yUR c)) (flip_bit (snd (yUF c)) (flip_bit (snd (yUL c))
    (flip_bit (snd (yUB c)) (flip_bit (snd (yDR c)) (flip_bit (snd (yDF c))
      (flip_bit (snd (yDL c)) (flip_bit (snd (yDB c)) (flip_bit (snd (yFR c))
        (flip_bit (snd (yFL c)) (flip_bit (snd (yBL c))
          (flip_bit (snd (yBR c)) 0))))))))))).

(** The index read off a cube is the index of that cube's flips. *)
Lemma flip_index_key c : flip_index c = flip_key (flips c).
Proof. destruct c; reflexivity. Qed.

(** Passing its check makes the edge-orientation heuristic safe. *)
Theorem flip_h_admissible :
  consistentb flip_step flip_goal flip_dom flip_h = true ->
  admissible_on flip_step flip_goal flip_dom flip_h.
Proof.
  intro H; apply consistentb_admissible; [apply flip_dom_closed | exact H].
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
  | _ => csolved
  end.

(** Reading the mask back off such a cube returns it unchanged. *)
Lemma is_slice_pick (b : bool) : is_slice (slice_piece b) = b.
Proof. destruct b; reflexivity. Qed.

(** How one move acts on the slice occupancy alone. *)
Definition slice_move (m : move) (l : list bool) : list bool :=
  slice_mask (cm2f m (embed_slice l)).

(** Which slots hold slice edges moves the same way whatever else is going on. *)
Theorem slice_mask_cm2f m c : slice_mask (cm2f m c) = slice_move m (slice_mask c).
Proof.
  unfold slice_move; destruct_cube c; destruct m as [f a]; destruct f, a;
    unfold slice_mask, epieces, embed_slice; cbn [eslots cm2f cquarter
      yUR yUF yUL yUB yDR yDF yDL yDB yFR yFL yBL yBR map];
    rewrite ?eshift_fst; cbn [fst];
    rewrite !is_slice_pick; reflexivity.
Qed.

(** The eighteen occupancy masks one move away. *)
Definition slice_step (l : list bool) : list (list bool) :=
  map (fun m => slice_move m l) Movel1.

(** The first phase is done with the slice when its four edges are back in
    it. *)
Definition slice_goal (l : list bool) : bool :=
  if list_eq_dec Bool.bool_dec l slice_home then true else false.

(** The whole space of twelve-slot masks. *)
Definition slice_dom : list (list bool) := tuples 12 [true; false].

(** A turn keeps the mask twelve slots wide. *)
Lemma slice_move_length m l : length (slice_move m l) = 12.
Proof.
  unfold slice_move, slice_mask, epieces, eslots; rewrite !length_map; reflexivity.
Qed.

(** So stepping stays inside the space. *)
Lemma slice_dom_closed x y :
  In x slice_dom -> In y (slice_step x) -> In y slice_dom.
Proof.
  intros _ Hy; apply in_map_iff in Hy as [m [<- _]].
  apply tuples_complete; [intros [|]; simpl; tauto | apply slice_move_length].
Qed.

(** One bit per slot, set when a slice edge sits there. *)
Definition slice_bit (e : edge) (k : nat) : nat := if is_slice e then 1 + 2 * k else 2 * k.

(** The mask read as a binary numeral. *)
Fixpoint slice_key (l : list bool) : nat :=
  match l with [] => 0 | b :: r => (if b then 1 + 2 * slice_key r else 2 * slice_key r) end.

(** Distances to the slice being intact. *)
Definition slice_table : table := build slice_step slice_key 30 [slice_home].

(** How far the slice edges still have to travel. *)
Definition slice_h (l : list bool) : nat := tget slice_table (slice_key l).

(** The occupancy index read straight off a cube's slots. *)
Definition slice_index (c : cube) : nat :=
  slice_bit (fst (yUR c)) (slice_bit (fst (yUF c)) (slice_bit (fst (yUL c))
    (slice_bit (fst (yUB c)) (slice_bit (fst (yDR c)) (slice_bit (fst (yDF c))
      (slice_bit (fst (yDL c)) (slice_bit (fst (yDB c)) (slice_bit (fst (yFR c))
        (slice_bit (fst (yFL c)) (slice_bit (fst (yBL c))
          (slice_bit (fst (yBR c)) 0))))))))))).

(** And it agrees with the index of that cube's mask. *)
Lemma slice_index_key c : slice_index c = slice_key (slice_mask c).
Proof. destruct c; reflexivity. Qed.

(** Passing its check makes the slice heuristic safe. *)
Theorem slice_h_admissible :
  consistentb slice_step slice_goal slice_dom slice_h = true ->
  admissible_on slice_step slice_goal slice_dom slice_h.
Proof.
  intro H; apply consistentb_admissible; [apply slice_dom_closed | exact H].
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
Definition embed_cperm (l : list corner) : cube :=
  match l with
  | [a; b; c; d; e; f; g; h] =>
      Cube (a, T0) (b, T0) (c, T0) (d, T0) (e, T0) (f, T0) (g, T0) (h, T0)
           (UR, F0) (UF, F0) (UL, F0) (UB, F0) (DR, F0) (DF, F0)
           (DL, F0) (DB, F0) (FR, F0) (FL, F0) (BL, F0) (BR, F0)
  | _ => csolved
  end.

(** How one move rearranges the corners. *)
Definition cperm_move (m : move) (l : list corner) : list corner :=
  cpieces (cm2f m (embed_cperm l)).

(** Where the corners sit moves the same way whatever else is going on. *)
Theorem cpieces_cm2f m c : cpieces (cm2f m c) = cperm_move m (cpieces c).
Proof.
  unfold cperm_move; destruct_cube c; destruct m as [f a]; destruct f, a;
    unfold cpieces, embed_cperm; cbn [cslots cm2f cquarter
      xURF xUFL xULB xUBR xDFR xDLF xDBL xDRB map];
    rewrite ?cshift_fst; cbn [fst]; reflexivity.
Qed.

(** The ten placements one allowed move away. *)
Definition cperm_step (l : list corner) : list (list corner) :=
  map (fun m => cperm_move m l) Movel2.

(** The corners are done when each is back in its own slot. *)
Definition cperm_goal (l : list corner) : bool :=
  if list_eq_dec corner_eq_dec l all_corners then true else false.

(** Every rearrangement of the eight corners. *)
Definition cperm_dom : list (list corner) := perms all_corners.

(** A turn rearranges the eight corners, so it cannot leave the space of
    rearrangements. *)
Lemma cperm_move_perm m l :
  In l cperm_dom -> Permutation l (cperm_move m l).
Proof.
  intro Hl; apply perms_sound in Hl.
  assert (Hlen : length l = 8)
    by (rewrite <- (Permutation_length Hl); reflexivity).
  destruct l as [| a1 [| a2 [| a3 [| a4 [| a5 [| a6 [| a7 [| a8 [| a9 l]]]]]]]]];
    simpl in Hlen; try discriminate.
  destruct m as [f t]; destruct f, t;
    unfold cperm_move, cpieces, embed_cperm;
    cbn [cslots cm2f cquarter xURF xUFL xULB xUBR xDFR xDLF xDBL xDRB map];
    rewrite ?cshift_fst; cbn [fst];
    apply (Permutation_count_occ corner_eq_dec); intro x; cbn;
    repeat (destruct (corner_eq_dec _ x)); lia.
Qed.

(** A turn rearranges corners, so stepping stays among rearrangements. *)
Lemma cperm_dom_closed x y :
  In x cperm_dom -> In y (cperm_step x) -> In y cperm_dom.
Proof.
  intros Hx Hy; apply in_map_iff in Hy as [m [<- _]].
  apply perms_complete, perm_trans with x;
    [apply perms_sound, Hx | apply cperm_move_perm, Hx].
Qed.

(** Index a placement by reading the slots as a base-eight numeral. The key
    space is larger than the 40320 placements that occur, which costs nothing:
    the table is a radix tree and never stores an index it was not given. *)
Definition corner_bits (x : corner) (k : nat) : nat :=
  match x with
  | URF => 8 * k | UFL => 1 + 8 * k | ULB => 2 + 8 * k | UBR => 3 + 8 * k
  | DFR => 4 + 8 * k | DLF => 5 + 8 * k | DBL => 6 + 8 * k | DRB => 7 + 8 * k
  end.

(** Three bits per corner. *)
Fixpoint cperm_key (l : list corner) : nat :=
  match l with [] => 0 | x :: r => corner_bits x (cperm_key r) end.

(** Distances to the corners being home, under the second phase's moves. *)
Definition cperm_table : table := build cperm_step cperm_key 30 [all_corners].

(** How far the corners still have to travel. *)
Definition cperm_h (l : list corner) : nat := tget cperm_table (cperm_key l).

(** The corner placement index read straight off a cube's slots. *)
Definition cperm_index (c : cube) : nat :=
  corner_bits (fst (xURF c)) (corner_bits (fst (xUFL c)) (corner_bits (fst (xULB c))
    (corner_bits (fst (xUBR c)) (corner_bits (fst (xDFR c)) (corner_bits (fst (xDLF c))
      (corner_bits (fst (xDBL c)) (corner_bits (fst (xDRB c)) 0))))))).

(** And it agrees with the index of that cube's corners. *)
Lemma cperm_index_key c : cperm_index c = cperm_key (cpieces c).
Proof. destruct c; reflexivity. Qed.

(** Passing its check makes the corner-placement heuristic safe. *)
Theorem cperm_h_admissible :
  consistentb cperm_step cperm_goal cperm_dom cperm_h = true ->
  admissible_on cperm_step cperm_goal cperm_dom cperm_h.
Proof.
  intro H; apply consistentb_admissible; [apply cperm_dom_closed | exact H].
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
Definition embed_e8 (l : list edge) : cube :=
  match l with
  | [a; b; c; d; e; f; g; h] =>
      Cube (URF, T0) (UFL, T0) (ULB, T0) (UBR, T0)
           (DFR, T0) (DLF, T0) (DBL, T0) (DRB, T0)
           (a, F0) (b, F0) (c, F0) (d, F0) (e, F0) (f, F0) (g, F0) (h, F0)
           (FR, F0) (FL, F0) (BL, F0) (BR, F0)
  | _ => csolved
  end.

(** A cube with the slice edges placed as given. *)
Definition embed_e4 (l : list edge) : cube :=
  match l with
  | [a; b; c; d] =>
      Cube (URF, T0) (UFL, T0) (ULB, T0) (UBR, T0)
           (DFR, T0) (DLF, T0) (DBL, T0) (DRB, T0)
           (UR, F0) (UF, F0) (UL, F0) (UB, F0) (DR, F0) (DF, F0)
           (DL, F0) (DB, F0) (a, F0) (b, F0) (c, F0) (d, F0)
  | _ => csolved
  end.

(** How one allowed move rearranges the non-slice edges. *)
Definition e8_move (m : move) (l : list edge) : list edge :=
  e8pieces (cm2f m (embed_e8 l)).

(** And the slice edges. *)
Definition e4_move (m : move) (l : list edge) : list edge :=
  e4pieces (cm2f m (embed_e4 l)).

(** Both groups move on their own, so long as the move is one the second phase
    is allowed: those are exactly the moves that keep the groups apart. *)
Theorem e8pieces_cm2f m c :
  phase2 m = true -> e8pieces (cm2f m c) = e8_move m (e8pieces c).
Proof.
  destruct m as [f a]; destruct f, a; try discriminate; intros _;
    unfold e8_move; destruct_cube c;
    unfold e8pieces, epieces, embed_e8; cbn [eslots cm2f cquarter
      yUR yUF yUL yUB yDR yDF yDL yDB yFR yFL yBL yBR map firstn];
    rewrite ?eshift_fst; cbn [fst]; reflexivity.
Qed.

(** The slice edges move on their own too, for the same reason. *)
Theorem e4pieces_cm2f m c :
  phase2 m = true -> e4pieces (cm2f m c) = e4_move m (e4pieces c).
Proof.
  destruct m as [f a]; destruct f, a; try discriminate; intros _;
    unfold e4_move; destruct_cube c;
    unfold e4pieces, epieces, embed_e4; cbn [eslots cm2f cquarter
      yUR yUF yUL yUB yDR yDF yDL yDB yFR yFL yBL yBR map skipn];
    rewrite ?eshift_fst; cbn [fst]; reflexivity.
Qed.

(** The ten placements one allowed move away. *)
Definition e8_step (l : list edge) : list (list edge) :=
  map (fun m => e8_move m l) Movel2.

(** Likewise for the slice. *)
Definition e4_step (l : list edge) : list (list edge) :=
  map (fun m => e4_move m l) Movel2.

(** The non-slice edges are done when each is back in its own slot. *)
Definition e8_goal (l : list edge) : bool :=
  if list_eq_dec edge_eq_dec l ud_edges then true else false.

(** Likewise for the slice edges. *)
Definition e4_goal (l : list edge) : bool :=
  if list_eq_dec edge_eq_dec l slice_edges then true else false.

(** Every rearrangement of the eight non-slice edges. *)
Definition e8_dom : list (list edge) := perms ud_edges.
(** And of the four slice edges. *)
Definition e4_dom : list (list edge) := perms slice_edges.

(** An allowed move rearranges the eight without letting any escape. *)
Lemma e8_move_perm m l :
  phase2 m = true -> In l e8_dom -> Permutation l (e8_move m l).
Proof.
  intros Hm Hl; apply perms_sound in Hl.
  assert (Hlen : length l = 8)
    by (rewrite <- (Permutation_length Hl); reflexivity).
  destruct l as [| a1 [| a2 [| a3 [| a4 [| a5 [| a6 [| a7 [| a8 [| a9 l]]]]]]]]];
    simpl in Hlen; try discriminate.
  destruct m as [f t]; destruct f, t; try discriminate;
    unfold e8_move, e8pieces, epieces, embed_e8;
    cbn [eslots cm2f cquarter yUR yUF yUL yUB yDR yDF yDL yDB
         yFR yFL yBL yBR map firstn];
    rewrite ?eshift_fst; cbn [fst];
    apply (Permutation_count_occ edge_eq_dec); intro x; cbn;
    repeat (destruct (edge_eq_dec _ x)); lia.
Qed.

(** And rearranges the four within the slice. *)
Lemma e4_move_perm m l :
  phase2 m = true -> In l e4_dom -> Permutation l (e4_move m l).
Proof.
  intros Hm Hl; apply perms_sound in Hl.
  assert (Hlen : length l = 4)
    by (rewrite <- (Permutation_length Hl); reflexivity).
  destruct l as [| a1 [| a2 [| a3 [| a4 [| a5 l]]]]]; simpl in Hlen; try discriminate.
  destruct m as [f t]; destruct f, t; try discriminate;
    unfold e4_move, e4pieces, epieces, embed_e4;
    cbn [eslots cm2f cquarter yUR yUF yUL yUB yDR yDF yDL yDB
         yFR yFL yBL yBR map skipn];
    rewrite ?eshift_fst; cbn [fst];
    apply (Permutation_count_occ edge_eq_dec); intro x; cbn;
    repeat (destruct (edge_eq_dec _ x)); lia.
Qed.

(** So stepping stays among rearrangements. *)
Lemma e8_dom_closed x y : In x e8_dom -> In y (e8_step x) -> In y e8_dom.
Proof.
  intros Hx Hy; apply in_map_iff in Hy as [m [<- Hm]].
  apply perms_complete, perm_trans with x;
    [apply perms_sound, Hx | apply e8_move_perm; auto using Movel2_phase2].
Qed.

(** Likewise for the slice. *)
Lemma e4_dom_closed x y : In x e4_dom -> In y (e4_step x) -> In y e4_dom.
Proof.
  intros Hx Hy; apply in_map_iff in Hy as [m [<- Hm]].
  apply perms_complete, perm_trans with x;
    [apply perms_sound, Hx | apply e4_move_perm; auto using Movel2_phase2].
Qed.

(** Four bits per edge. *)
Definition edge_bits (x : edge) (k : nat) : nat :=
  match x with
  | UR => 16 * k | UF => 1 + 16 * k | UL => 2 + 16 * k | UB => 3 + 16 * k
  | DR => 4 + 16 * k | DF => 5 + 16 * k | DL => 6 + 16 * k | DB => 7 + 16 * k
  | FR => 8 + 16 * k | FL => 9 + 16 * k | BL => 10 + 16 * k | BR => 11 + 16 * k
  end.

(** A tuple of edges read as a numeral. *)
Fixpoint edge_key (l : list edge) : nat :=
  match l with [] => 0 | x :: r => edge_bits x (edge_key r) end.

(** Indexing the non-slice placement. *)
Definition e8_key (l : list edge) : nat := edge_key l.
(** And the slice placement. *)
Definition e4_key (l : list edge) : nat := edge_key l.

(** Distances to the non-slice edges being home. *)
Definition e8_table : table := build e8_step e8_key 30 [ud_edges].
(** And to the slice edges being home. *)
Definition e4_table : table := build e4_step e4_key 30 [slice_edges].

(** The placement indices read straight off a cube's slots. *)
Definition e8_index (c : cube) : nat :=
  edge_bits (fst (yUR c)) (edge_bits (fst (yUF c)) (edge_bits (fst (yUL c))
    (edge_bits (fst (yUB c)) (edge_bits (fst (yDR c)) (edge_bits (fst (yDF c))
      (edge_bits (fst (yDL c)) (edge_bits (fst (yDB c)) 0))))))).

(** The slice placement index, likewise. *)
Definition e4_index (c : cube) : nat :=
  edge_bits (fst (yFR c)) (edge_bits (fst (yFL c)) (edge_bits (fst (yBL c))
    (edge_bits (fst (yBR c)) 0))).

(** Both agree with the indices of the cube's own edge tuples. *)
Lemma e8_index_key c : e8_index c = e8_key (e8pieces c).
Proof. destruct c; reflexivity. Qed.

(** Likewise for the slice. *)
Lemma e4_index_key c : e4_index c = e4_key (e4pieces c).
Proof. destruct c; reflexivity. Qed.

(** How far the non-slice edges still have to travel. *)
Definition e8_h (l : list edge) : nat := tget e8_table (e8_key l).
(** And the slice edges. *)
Definition e4_h (l : list edge) : nat := tget e4_table (e4_key l).

(** Passing their checks makes the edge-placement heuristics safe. *)
Theorem e8_h_admissible :
  consistentb e8_step e8_goal e8_dom e8_h = true ->
  admissible_on e8_step e8_goal e8_dom e8_h.
Proof.
  intro H; apply consistentb_admissible; [apply e8_dom_closed | exact H].
Qed.

(** Passing its check makes the slice heuristic safe too. *)
Theorem e4_h_admissible :
  consistentb e4_step e4_goal e4_dom e4_h = true ->
  admissible_on e4_step e4_goal e4_dom e4_h.
Proof.
  intro H; apply consistentb_admissible; [apply e4_dom_closed | exact H].
Qed.
