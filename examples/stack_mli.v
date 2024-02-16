Set Implicit Arguments.

Require Import Gospel.

Require Coq.ZArith.BinInt TLC.LibLogic TLC.LibRelation TLC.LibInt TLC.LibListZ.

Require Import CFML.SepBase CFML.SepLifted CFML.WPLib CFML.WPLifted CFML.WPRecord CFML.WPArray CFML.WPBuiltin.

Require CFML.Stdlib.Array_ml CFML.Stdlib.List_ml CFML.Stdlib.Sys_ml.

Require Import Coq.ZArith.BinIntDef CFML.Semantics CFML.WPHeader.

Delimit Scope Z_scope with Z.

Parameter T :
  Coq.Lists.List.list int ->
  loc -> CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hprop.

Parameter create : CFML.Semantics.val.

Parameter _create_spec :
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps create (
      Coq.Lists.List.cons (
        @CFML.SepLifted.dyn_make CFML.Semantics.val _ Coq.Init.Datatypes.tt
      ) Coq.Lists.List.nil
    )
  ) CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hempty (
    fun _loc_q : loc =>
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hexists (
      fun q : Coq.Lists.List.list int =>
      CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
        CFML.SepBase.SepBasicSetup.HS.repr (T q) _loc_q
      ) (
        CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (
          Coq.Init.Logic.eq q Coq.Lists.List.nil
        )
      )
    )
  ).

Parameter push : CFML.Semantics.val.

Parameter _push_spec :
  forall _loc_q : loc,
  forall q : Coq.Lists.List.list int,
  forall x : int,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps push (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make loc _ _loc_q) (
        Coq.Lists.List.cons (@CFML.SepLifted.dyn_make int _ x) Coq.Lists.List.nil
      )
    )
  ) (CFML.SepBase.SepBasicSetup.HS.repr (T q) _loc_q) (
    fun __UNUSED__ : CFML.Semantics.val =>
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hexists (
      fun _q' : Coq.Lists.List.list int =>
      CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
        CFML.SepBase.SepBasicSetup.HS.repr (T _q') _loc_q
      ) (
        CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (
          Coq.Init.Logic.eq _q' (Coq.Lists.List.cons x q)
        )
      )
    )
  ).

Parameter pop_opt : CFML.Semantics.val.

Parameter _pop_opt_spec :
  forall _loc_q : loc,
  forall q : Coq.Lists.List.list int,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps pop_opt (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make loc _ _loc_q) Coq.Lists.List.nil
    )
  ) (CFML.SepBase.SepBasicSetup.HS.repr (T q) _loc_q) (
    fun r : Coq.Init.Datatypes.option int =>
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hexists (
      fun _q' : Coq.Lists.List.list int =>
      CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
        CFML.SepBase.SepBasicSetup.HS.repr (T _q') _loc_q
      ) (
        CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (
          match r with
          | Coq.Init.Datatypes.None => Coq.Init.Logic.and (
              Coq.Init.Logic.eq q Coq.Lists.List.nil
            ) (Coq.Init.Logic.eq _q' Coq.Lists.List.nil)
            | Coq.Init.Datatypes.Some r_val => Coq.Init.Logic.eq q (
              Coq.Lists.List.cons r_val _q'
            )
            end
        )
      )
    )
  ).

Parameter top_opt : CFML.Semantics.val.

Parameter _top_opt_spec :
  forall _loc_q : loc,
  forall q : Coq.Lists.List.list int,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps top_opt (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make loc _ _loc_q) Coq.Lists.List.nil
    )
  ) (CFML.SepBase.SepBasicSetup.HS.repr (T q) _loc_q) (
    fun r : Coq.Init.Datatypes.option int =>
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hexists (
      fun q : Coq.Lists.List.list int =>
      CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
        CFML.SepBase.SepBasicSetup.HS.repr (T q) _loc_q
      ) (
        CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (
          match r with
          | Coq.Init.Datatypes.None => Coq.Init.Logic.eq q Coq.Lists.List.nil
            | Coq.Init.Datatypes.Some r => Coq.Init.Logic.and (
              Coq.Init.Logic.not (Coq.Init.Logic.eq q Coq.Lists.List.nil)
            ) (Coq.Init.Logic.eq r (Gospel.hd_gospel q))
            end
        )
      )
    )
  ).

Parameter clear : CFML.Semantics.val.

Parameter _clear_spec :
  forall _loc_q : loc,
  forall q : Coq.Lists.List.list int,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps clear (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make loc _ _loc_q) Coq.Lists.List.nil
    )
  ) (CFML.SepBase.SepBasicSetup.HS.repr (T q) _loc_q) (
    fun __UNUSED__ : CFML.Semantics.val =>
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hexists (
      fun _q' : Coq.Lists.List.list int =>
      CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
        CFML.SepBase.SepBasicSetup.HS.repr (T _q') _loc_q
      ) (
        CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (
          Coq.Init.Logic.eq _q' Coq.Lists.List.nil
        )
      )
    )
  ).

Parameter copy : CFML.Semantics.val.

Parameter _copy_spec :
  forall _loc_q1 : loc,
  forall q1 : Coq.Lists.List.list int,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps copy (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make loc _ _loc_q1) Coq.Lists.List.nil
    )
  ) (CFML.SepBase.SepBasicSetup.HS.repr (T q1) _loc_q1) (
    fun _loc_q2 : loc =>
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hexists (
      fun q1 : Coq.Lists.List.list int =>
      CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hexists (
        fun q2 : Coq.Lists.List.list int =>
        CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
          CFML.SepBase.SepBasicSetup.HS.repr (T q1) _loc_q1
        ) (
          CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
            CFML.SepBase.SepBasicSetup.HS.repr (T q2) _loc_q2
          ) (
            CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (
              Coq.Init.Logic.eq q2 q1
            )
          )
        )
      )
    )
  ).

Parameter is_empty : CFML.Semantics.val.

Parameter _is_empty_spec :
  forall _loc_q : loc,
  forall q : Coq.Lists.List.list int,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps is_empty (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make loc _ _loc_q) Coq.Lists.List.nil
    )
  ) (CFML.SepBase.SepBasicSetup.HS.repr (T q) _loc_q) (
    fun b : bool =>
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hexists (
      fun q : Coq.Lists.List.list int =>
      CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
        CFML.SepBase.SepBasicSetup.HS.repr (T q) _loc_q
      ) (
        CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (
          Coq.Init.Logic.eq b true -> Coq.Init.Logic.eq q Coq.Lists.List.nil
        )
      )
    )
  ).

Parameter length : CFML.Semantics.val.

Parameter _length_spec :
  forall _loc_q : loc,
  forall q : Coq.Lists.List.list int,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps length (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make loc _ _loc_q) Coq.Lists.List.nil
    )
  ) (CFML.SepBase.SepBasicSetup.HS.repr (T q) _loc_q) (
    fun l : int =>
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hexists (
      fun q : Coq.Lists.List.list int =>
      CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
        CFML.SepBase.SepBasicSetup.HS.repr (T q) _loc_q
      ) (
        CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (
          Coq.Init.Logic.eq (LibListZ.length q) l
        )
      )
    )
  ).

Parameter transfer : CFML.Semantics.val.

Parameter _transfer_spec :
  forall _loc_q1 : loc,
  forall q1 : Coq.Lists.List.list int,
  forall _loc_q2 : loc,
  forall q2 : Coq.Lists.List.list int,
  CFML.SepLifted.Triple (
    CFML.SepLifted.Trm_apps transfer (
      Coq.Lists.List.cons (@CFML.SepLifted.dyn_make loc _ _loc_q1) (
        Coq.Lists.List.cons (@CFML.SepLifted.dyn_make loc _ _loc_q2) Coq.Lists.List.nil
      )
    )
  ) (
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
      CFML.SepBase.SepBasicSetup.HS.repr (T q1) _loc_q1
    ) (CFML.SepBase.SepBasicSetup.HS.repr (T q2) _loc_q2)
  ) (
    fun __UNUSED__ : CFML.Semantics.val =>
    CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hexists (
      fun _q1' : Coq.Lists.List.list int =>
      CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hexists (
        fun _q2' : Coq.Lists.List.list int =>
        CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
          CFML.SepBase.SepBasicSetup.HS.repr (T _q1') _loc_q1
        ) (
          CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
            CFML.SepBase.SepBasicSetup.HS.repr (T _q2') _loc_q2
          ) (
            CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hstar (
              CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (
                Coq.Init.Logic.eq _q1' Coq.Lists.List.nil
              )
            ) (
              CFML.SepBase.SepBasicSetup.SepSimplArgsCredits.hpure (
                Coq.Init.Logic.eq _q2' (Coq.Lists.List.app _q2' q1)
              )
            )
          )
        )
      )
    )
  ).


