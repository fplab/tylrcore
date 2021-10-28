Require Import Coq.Lists.List.

Module ListFrame.
  Definition t (A:Type) := (list A * list A) % type.

  Definition fill {A:Type} (subj : list A) (frame : t A) :=
    let (prefix, suffix) := frame in
    rev prefix ++ subj ++ suffix.
End ListFrame.

Inductive sort : Type :=
| Pat : sort
| Exp : sort.

Module Term.
  Inductive t : sort -> Type :=
  | Op_hole : forall s, t s
  | Op_text : forall s, t s
  | Bin_hole : forall s, t s -> t s -> t s
  | Bin_text : forall s, t s -> t s -> t s
  | Paren : forall s, t s -> t s
  | Lam : t Pat -> t Exp -> t Exp
  | Let : t Pat -> t Exp -> t Exp -> t Exp.
  (* Inductive pat : Type :=
  | Op_hole_p : pat
  | Op_text_p : pat
  | Bin_hole_p : pat -> pat -> pat
  | Bin_text_p : pat -> pat -> pat
  | Paren_p : pat -> pat.
  Inductive exp : Type :=
  | Op_hole_e : exp
  | Op_text_e : exp
  | Bin_hole_e : exp -> exp -> exp
  | Bin_text_e : exp -> exp -> exp
  | Paren_e : exp -> exp
  | Lam : pat -> exp -> exp
  | Let : pat -> exp -> exp -> exp. *)
End Term.

Module Tile.
  Inductive t : sort -> Type :=
  | Op_hole : forall s, t s
  | Op_text : forall s, t s
  | Bin_hole : forall s, t s
  | Bin_text : forall s, t s
  | Paren : forall s, list (t s) -> t s
  | Lam : list (t Pat) -> t Exp
  | Let : list (t Pat) -> list (t Exp) -> t Exp.
  (* Inductive pat : Type :=
  | Op_hole_p : pat
  | Op_text_p : pat
  | Bin_hole_p : pat
  | Bin_text_p : pat
  | Paren_p : list pat -> pat.
  Inductive exp : Type :=
  | Op_hole_e : exp
  | Op_text_e : exp
  | Bin_hole_e : exp
  | Bin_text_e : exp
  | Paren_e : list exp -> exp
  | Lam : list pat -> exp
  | Let : list pat -> list exp -> exp.
  Inductive t : Type :=
  | Pat : pat -> t
  | Exp : exp -> t. *)
End Tile.

Module Shard.
  Inductive t : sort -> Type :=
  | Paren_l : forall s, t s
  | Paren_r : forall s, t s
  | Lam_lam : t Exp
  | Lam_dot : t Exp
  | Let_let : t Exp
  | Let_eq : t Exp
  | Let_in : t Exp.
  (* Inductive pat : Type :=
  | Paren_l_p : pat
  | Paren_r_p : pat.
  Inductive exp : Type :=
  | Paren_l_e : exp
  | Paren_r_e : exp
  | Lam_lam : exp
  | Lam_dot : exp
  | Let_let : exp
  | Let_eq : exp
  | Let_in : exp.
  Inductive t : Type :=
  | Pat : pat -> t
  | Exp : exp -> t. *)
End Shard.

Module Piece.
  Inductive t : Type :=
  | Tile : forall s, Tile.t s -> t
  | Shard : forall s, Shard.t s -> t.

  (* TODO *)
  Inductive atomic : t -> Prop :=
  | todo : forall c, atomic c.
End Piece.

Module Segment.
  Definition t := list Piece.t.
  Definition affixes := ListFrame.t Piece.t.

  Definition of_tiles {s:sort} (tiles : list (Tile.t s)) : t :=
    map (Piece.Tile s) tiles.

  (* TODO *)
  Definition is_intact (segment: t) : bool := true.
  (* Inductive intact : t -> Prop :=
  | intact_nil : intact nil
  | intact_cons : forall sort tile pieces, intact pieces -> intact (Piece.Tile sort tile::pieces). *)

  Inductive same_sort_capped : t -> Prop :=
  | todo : forall segment, same_sort_capped segment.

  (* TODO *)
  Definition assemble (segment: t) : t :=
    segment.
End Segment.

Module Frame.
  Inductive seq : sort -> Type :=
  | Seq : forall s, ListFrame.t (Tile.t s) -> t s -> seq s
  with t : sort -> Type :=
  | Root : t Exp
  | Paren_body : forall s, seq s -> t s
  | Lam_pat : seq Exp -> t Pat
  | Let_pat : list (Tile.t Exp) -> seq Exp -> t Pat
  | Let_def : list (Tile.t Pat) -> seq Exp -> t Exp.

  (* TODO do I need this forall s? couldn't get implicit arg to work *)
  Inductive fills : forall s, Segment.t -> t s -> Segment.t -> Prop :=
  | fills_root : forall segment, fills Exp segment Root segment
  | fills_Paren_body : forall s body affixes frame filled,
      fills s (Segment.of_tiles (ListFrame.fill (Tile.Paren s body::nil) affixes)) frame filled
      -> fills s (Segment.of_tiles body) (Paren_body s (Seq s affixes frame)) filled.
  (* TODO *)
End Frame.

Module Subject.
  Inductive t : Type :=
  | Pointing : Segment.affixes -> t
  | Selecting : Segment.t -> Segment.affixes -> t
  | Restructuring : Segment.t -> Segment.affixes -> t.

  Definition erase (subj: t) : Segment.t :=
    match subj with
    | Pointing affixes => ListFrame.fill nil affixes
    | Selecting selection affixes => Segment.assemble (ListFrame.fill selection affixes)
    | Restructuring selection affixes =>
      if Segment.is_intact selection
      then ListFrame.fill nil affixes
      else Segment.assemble (ListFrame.fill selection affixes)
    end.
End Subject.

Module Zipper.
  (* TODO is this forall s right? *)
  Definition t (s : sort) := (Subject.t * Frame.t s) % type.

  (* TODO *)
  Inductive erases: forall s, t s -> Segment.t -> Prop :=
  | er : erases Exp (Subject.Pointing (nil, nil), Frame.Root) nil.
End Zipper.

Module Direction.
  Inductive t : Type :=
  | L : t
  | R : t.
End Direction.

Module Holes.
  (* TODO *)
  Definition fix_holes (s : sort) (affixes : Segment.affixes) := affixes.
End Holes.

Module Action.
  Inductive t : Type :=
  | Mark : t
  | Move : Direction.t -> t
  | Insert : forall s, Tile.t s -> t
  | Remove : t.

  Inductive move_pointing : forall (s1 s2 : sort), (Zipper.t s1) -> Direction.t -> (Zipper.t s2) -> Prop :=
  | p_move_r_atomic : forall s prefix piece suffix frame,
      Piece.atomic piece
      -> move_pointing
          s s
          (Subject.Pointing (prefix, (piece::suffix)), frame)
          Direction.R
          (Subject.Pointing ((piece::prefix), suffix), frame).
  (* TODO *)

  Inductive move_selecting : forall (s1 s2 : sort), (Zipper.t s1) -> Direction.t -> (Zipper.t s2) -> Prop :=
  | todo_selecting : forall s d zipper, move_selecting s s zipper d zipper.

  Inductive move_restructuring : forall (s1 s2 : sort), (Zipper.t s1) -> Direction.t -> (Zipper.t s2) -> Prop :=
  | todo_restructuring : forall s d zipper, move_restructuring s s zipper d zipper.

  Inductive perform : forall (s1 s2 : sort), (Zipper.t s1) -> Action.t -> (Zipper.t s2) -> Prop :=
  | move : forall s1 s2 d affixes frame zipper,
      move_pointing s1 s2 (Subject.Pointing affixes, frame) d zipper
      -> perform s1 s2 (Subject.Pointing affixes, frame) (Move d) zipper
  | insert : forall s tile prefix suffix frame,
      perform s s
        (Subject.Pointing (prefix, suffix), frame)
        (Insert s tile)
        (Subject.Pointing (Holes.fix_holes s (prefix, Piece.Tile s tile::suffix)), frame)
  | start_selecting : forall s affixes frame,
      perform s s
        (Subject.Pointing affixes, frame)
        Mark
        (Subject.Selecting nil affixes, frame)
  | select : forall d s1 s2 selection affixes frame zipper,
      move_selecting s1 s2 (Subject.Selecting selection affixes, frame) d zipper
      -> perform s1 s2 (Subject.Selecting selection affixes, frame) (Move d) zipper
  | pick_up : forall s selection affixes frame,
      Segment.same_sort_capped selection
      -> perform s s
            (Subject.Selecting selection affixes, frame)
            Mark
            (Subject.Restructuring selection (Holes.fix_holes s affixes), frame)
  | restructure : forall s1 s2 d selection affixes frame zipper,
      move_restructuring s1 s2 (Subject.Restructuring selection affixes, frame) d zipper
      -> perform s1 s2 (Subject.Restructuring selection affixes, frame) (Move d) zipper.

End Action.

