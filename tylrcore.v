Require Import Coq.Lists.List.
Set Printing Matching.

Module ListFrame.
  Definition t (A:Type) := (list A * list A) % type.

  Definition fill {A:Type} (subj : list A) (frame : t A) :=
    let (prefix, suffix) := frame in
    rev prefix ++ subj ++ suffix.
End ListFrame.

Module Sort.
  Inductive t : Type :=
  | Pat : t
  | Exp : t.
End Sort.

Module Direction.
  Inductive t : Type :=
  | L : t
  | R : t.

  Definition toggle (d : t) :=
    match d with
    | L => R
    | R => L
    end.

  Definition choose {A : Type} (d : t) (p : A * A) :=
    let (l, r) := p in
    match d with
    | L => l
    | R => r
    end.
End Direction.

Module Tip.
  Definition t : Type := (Direction.t * Sort.t) % type.

  Definition sort (tip : t) : Sort.t := let (_, s) := tip in s.
End Tip.

Module Term.
  Inductive t : Sort.t -> Type :=
  | Op_hole : forall s, t s
  | Op_text : forall s, t s
  | Bin_hole : forall s, t s -> t s -> t s
  | Bin_text : forall s, t s -> t s -> t s
  | Paren : forall s, t s -> t s
  | Lam : t Sort.Pat -> t Sort.Exp -> t Sort.Exp
  | Let : t Sort.Pat -> t Sort.Exp -> t Sort.Exp -> t Sort.Exp.
End Term.

Module Tile.
  Inductive t : Sort.t -> Type :=
  | Op_hole : forall s, t s
  | Op_text : forall s, t s
  | Bin_hole : forall s, t s
  | Bin_text : forall s, t s
  | Paren : forall s, list (t s) -> t s
  | Lam : list (t Sort.Pat) -> t Sort.Exp
  | Let : list (t Sort.Pat) -> list (t Sort.Exp) -> t Sort.Exp.

  Section t_ind'.
    Variable P_t : forall s, t s -> Prop.
    Variable P_seq : forall s, list (t s) -> Prop.

    Variable P_seq_nil : forall s, P_seq s nil.
    Variable P_seq_cons : forall s hd tl, P_t s hd -> P_seq s tl -> P_seq s (hd :: tl).

    Variable P_Op_hole : forall s, P_t s (Op_hole s).
    Variable P_Op_text : forall s, P_t s (Op_text s).
    Variable P_Bin_hole : forall s, P_t s (Bin_hole s).
    Variable P_Bin_text : forall s, P_t s (Bin_text s).
    Variable P_Paren : forall s body, P_seq s body -> P_t s (Paren s body).
    Variable P_Lam : forall pat, P_seq Sort.Pat pat -> P_t Sort.Exp (Lam pat).
    Variable P_Let : forall pat def,
      P_seq Sort.Pat pat -> P_seq Sort.Exp def -> P_t Sort.Exp (Let pat def).

    Fixpoint t_ind' {s} (tile : t s) : P_t s tile.
    refine (
      match tile with
      | Op_hole _ => _
      | Op_text _ => _
      | Bin_hole _ => _
      | Bin_text _ => _
      | Paren _ body => _
      | Lam pat => _
      | Let pat def => _
      end
    ).
    - refine (P_Op_hole t).
    - refine (P_Op_text t).
    - refine (P_Bin_hole t).
    - refine (P_Bin_text t).
    - refine (P_Paren t body _).
      induction body; auto.
    - refine (P_Lam _ _).
      induction pat; auto.
    - refine (P_Let _ _ _ _).
      induction pat; auto.
      induction def; auto.
    Qed.
  End t_ind'.

  Definition tip {s:Sort.t} (d : Direction.t) (tile : t s) : Tip.t :=
    match (tile) with
    | Op_hole s | Op_text s | Paren s _ => (d, s)
    | Bin_hole s | Bin_text s => (Direction.toggle d, s)
    | Lam _
    | Let _ _ => (Direction.L, Sort.Exp)
    end.
End Tile.

Module Shard.
  Inductive t : Sort.t -> Type :=
  | Paren_l : forall s, t s
  | Paren_r : forall s, t s
  | Lam_lam : t Sort.Exp
  | Lam_dot : t Sort.Exp
  | Let_let : t Sort.Exp
  | Let_eq : t Sort.Exp
  | Let_in : t Sort.Exp.

  Definition tip {s:Sort.t} (d : Direction.t) (shard : t s) : Tip.t :=
    let choose := Direction.choose d in
    match shard with
    | Paren_l s => (Direction.L, s)
    | Paren_r s => (Direction.R, s)
    | Lam_lam
    | Let_let => (Direction.L, choose (Sort.Exp, Sort.Pat))
    | Lam_dot
    | Let_eq => (Direction.toggle d, choose (Sort.Pat, Sort.Exp))
    | Let_in => (Direction.toggle d, Sort.Exp)
    end.
End Shard.

Module Piece.
  Inductive t : Type :=
  | Tile : forall s, Tile.t s -> t
  | Shard : forall s, Shard.t s -> t.

  Definition tip (d : Direction.t) (piece : t) : Tip.t :=
    match piece with
    | Tile _ tile => Tile.tip d tile
    | Shard _ shard => Shard.tip d shard
    end.

  (* TODO *)
  Inductive atomic : t -> Prop :=
  | todo : forall c, atomic c.
End Piece.

Module Segment.
  Definition t := list Piece.t.
  Definition affixes := ListFrame.t Piece.t.

  Definition of_tiles {s:Sort.t} (tiles : list (Tile.t s)) : t :=
    map (Piece.Tile s) tiles.

  Definition tip (d : Direction.t) (segment : t) : Tip.t :=
    let dummy_piece := Piece.Tile Sort.Exp (Tile.Op_hole Sort.Exp) in
    match d with
    | Direction.L => Piece.tip d (hd dummy_piece segment)
    | Direction.R => Piece.tip d (last segment dummy_piece)
    end.

  (* TODO *)
  Definition intact (segment: t) : Prop := True.
  (* Inductive intact : t -> Prop :=
  | intact_nil : intact nil
  | intact_cons : forall sort tile pieces, intact pieces -> intact (Piece.Tile sort tile::pieces). *)
  Definition cracked (segment : t) : Prop := True.

  Definition intact_or_cracked : forall segment, { intact segment } + { cracked segment }.
  Admitted.

  Inductive same_sort_capped : t -> Prop :=
  | todo : forall segment, same_sort_capped segment.

  (* TODO *)
  Definition assemble (segment: t) : t :=
    segment.

  Definition filter_tiles (s : Sort.t) (segment : t) : t.
  Admitted.
End Segment.

Module Frame.
  Inductive seq : Sort.t -> Type :=
  | Seq : forall s, ListFrame.t (Tile.t s) -> tile s -> seq s
  with tile : Sort.t -> Type :=
  | Root : tile Sort.Exp
  | Paren_body : forall s, seq s -> tile s
  | Lam_pat : seq Sort.Exp -> tile Sort.Pat
  | Let_pat : list (Tile.t Sort.Exp) -> seq Sort.Exp -> tile Sort.Pat
  | Let_def : list (Tile.t Sort.Pat) -> seq Sort.Exp -> tile Sort.Exp.

  Inductive t : Type :=
  | F : forall s, tile s -> t.

  (* Fixpoint fill (segment : Segment.t) (frame : t) : option Segment.t :=
    let F s tile := frame in
    match tile with
    | Root => Some segment
    | Paren_body s' seq =>
      match Segment.
      let Seq _ affixes tile := seq in *)

  (* TODO do I need this forall s? couldn't get implicit arg to work *)
  Inductive fills : Segment.t -> t -> Segment.t -> Prop :=
  | fills_root : forall segment, fills segment (F Sort.Exp Root) segment
  | fills_Paren_body : forall s body affixes tile_frame filled,
      fills (Segment.of_tiles (ListFrame.fill (Tile.Paren s body::nil) affixes)) (F s tile_frame) filled
      -> fills (Segment.of_tiles body) (F s (Paren_body s (Seq s affixes tile_frame))) filled.
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
      if Segment.intact_or_cracked selection
      then ListFrame.fill nil affixes
      else Segment.assemble (ListFrame.fill selection affixes)
    end.
End Subject.

Module Zipper.
  (* TODO is this forall s right? *)
  Definition t := (Subject.t * Frame.t) % type.

  (* TODO *)
  Inductive erases: t -> Segment.t -> Prop :=
  | er : erases (Subject.Pointing (nil, nil), Frame.F Sort.Exp Frame.Root) nil.
End Zipper.

Module Disassembly.
  Definition step_disassemble_piece (c : Piece.t) : option Segment.t :=
    match c with
    | Piece.Shard _ _
    | Piece.Tile _ (Tile.Op_hole _ | Tile.Op_text _ | Tile.Bin_hole _ | Tile.Bin_text _) => None
    | Piece.Tile _ (Tile.Paren s body) =>
      let p := Piece.Shard s in
      Some (((p (Shard.Paren_l s)) :: Segment.of_tiles body) ++ (p (Shard.Paren_r s) :: nil))
    | Piece.Tile _ (Tile.Lam pat) =>
      let p := Piece.Shard Sort.Exp in
      Some ((p Shard.Lam_lam :: Segment.of_tiles pat) ++ (p Shard.Lam_dot :: nil))
    | Piece.Tile _ (Tile.Let pat def) =>
      let p := Piece.Shard Sort.Exp in
      Some(
        (p Shard.Let_let :: Segment.of_tiles pat)
        ++ (p Shard.Let_eq :: Segment.of_tiles def)
        ++ (p Shard.Let_in :: nil)
      )
    end.

  (* non-deterministic *)
  Inductive step_disassemble_segment : Segment.t -> Segment.t -> Prop :=
  | disassemble_hd : forall piece step_disassembled segment,
      step_disassemble_piece piece = Some step_disassembled
      -> step_disassemble_segment (piece :: segment) (step_disassembled ++ segment)
  | disassemble_tl : forall piece segment step_disassembled,
      step_disassemble_segment segment step_disassembled
      -> step_disassemble_segment (piece :: segment) (piece :: step_disassembled).

  (* Definition step_disassemble_frame () *)

End Disassembly.

Module Assembly.
  Definition assemble_segment : Segment.t -> Segment.t.
  Admitted.

  Definition assemble_zipper : Zipper.t -> Zipper.t.
  Admitted.
End Assembly.

Module Connected.
  Inductive connected : Tip.t -> Segment.t -> Tip.t -> Prop :=
  | connected_nil : forall tip, connected tip nil tip
  | connected_cons_atomic : forall piece segment tip,
      Disassembly.step_disassemble_piece piece = None
      -> connected (Piece.tip Direction.R piece) segment tip
      -> connected (Piece.tip Direction.L piece) (piece :: segment) tip
  | connected_cons_disassembles : forall tip_l piece segment' segment tip_r,
      Disassembly.step_disassemble_piece piece = Some segment'
      -> connected tip_l (segment' ++ segment) tip_r
      -> connected tip_l (piece :: segment) tip_r.

  Lemma connected_parts :
    forall tip0 segment1 segment2 tip2,
      connected tip0 (segment1 ++ segment2) tip2
      -> exists tip1, connected tip0 segment1 tip1 /\ connected tip1 segment2 tip2.
  Proof.
    induction segment1.
    - intros. exists tip0. split.
      + apply connected_nil.
      + rewrite app_nil_l in H. assumption.
    - Admitted.

  (* Lemma connected_parts :
    forall tip_l piece segment tip_r,
      connected tip_l (piece::segment) tip_r
      -> exists tip, connected tip_l (piece::nil) tip /\ connected tip segment tip_r *)

  Lemma cons_app_singleton {A : Type} :
    forall (x : A) (l : list A), x :: l = (x :: nil) ++ l.
  Proof.
  Admitted.

  Lemma connected_transitive :
    forall segment1 segment2 tip0 tip1 tip2,
      connected tip0 segment1 tip1
      -> connected tip1 segment2 tip2
      -> connected tip0 (segment1 ++ segment2) tip2.
  Proof.
    induction segment1.
    - intros. rewrite app_nil_l. inversion H. assumption.
    - intros. rewrite cons_app_singleton in H. apply connected_parts in H.
  Admitted.


  (* TODO *)
  Definition fix_ (s : Sort.t) (affixes : Segment.affixes) := affixes.
End Connected.

Module Action.
  Inductive t : Type :=
  | Mark : t
  | Move : Direction.t -> t
  | Insert : forall s, Tile.t s -> t
  | Remove : t.

  Inductive move_pointing : Zipper.t -> Direction.t -> Zipper.t -> Prop :=
  | p_move_r_atomic : forall prefix piece suffix frame,
      Piece.atomic piece
      -> move_pointing
          (Subject.Pointing (prefix, (piece::suffix)), frame)
          Direction.R
          (Subject.Pointing ((piece::prefix), suffix), frame).
  (* TODO *)

  Inductive move_selecting : Zipper.t -> Direction.t -> Zipper.t -> Prop :=
  | todo_selecting : forall d zipper, move_selecting zipper d zipper.

  Inductive move_restructuring : Zipper.t -> Direction.t -> Zipper.t -> Prop :=
  | todo_restructuring : forall d zipper, move_restructuring zipper d zipper.

  Inductive perform : Zipper.t -> Action.t -> Zipper.t -> Prop :=
  | move : forall d affixes frame zipper,
      move_pointing (Subject.Pointing affixes, frame) d zipper
      -> perform (Subject.Pointing affixes, frame) (Move d) zipper
  | insert : forall s tile prefix suffix tile_frame,
      perform
        (Subject.Pointing (prefix, suffix), Frame.F s tile_frame)
        (Insert s tile)
        (Subject.Pointing (Connected.fix_ s (prefix, Piece.Tile s tile::suffix)), Frame.F s tile_frame)
  | start_selecting : forall affixes frame,
      perform
        (Subject.Pointing affixes, frame)
        Mark
        (Subject.Selecting nil affixes, frame)
  | select : forall d selection affixes frame zipper,
      move_selecting (Subject.Selecting selection affixes, frame) d zipper
      -> perform (Subject.Selecting selection affixes, frame) (Move d) zipper
  | pick_up : forall s selection affixes tile_frame,
      Segment.same_sort_capped selection
      -> perform
            (Subject.Selecting selection affixes, Frame.F s tile_frame)
            Mark
            (Subject.Restructuring selection (Connected.fix_ s affixes), Frame.F s tile_frame)
  | restructure : forall d selection affixes frame zipper,
      move_restructuring (Subject.Restructuring selection affixes, frame) d zipper
      -> perform (Subject.Restructuring selection affixes, frame) (Move d) zipper
  | put_down : forall s selection prefix suffix prefix' suffix' tile_frame,
      (Tip.sort (Segment.tip Direction.L selection) = s)
      -> Connected.fix_ s (prefix, selection ++ suffix) = (prefix', suffix')
      -> perform
          (Subject.Restructuring selection (prefix, suffix), Frame.F s tile_frame)
          Mark
          (Assembly.assemble_zipper
            (Subject.Pointing (prefix', Assembly.assemble_segment suffix'), Frame.F s tile_frame))
  | remove : forall s selection prefix suffix prefix' suffix' tile_frame,
      Connected.fix_ s (Segment.filter_tiles s prefix, Segment.filter_tiles s suffix) = (prefix', suffix')
      -> perform
          (Subject.Restructuring selection (prefix, suffix), Frame.F s tile_frame)
          Remove
          (Subject.Pointing (prefix, suffix), Frame.F s tile_frame)
    .
End Action.

