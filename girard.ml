
(** Define the Type type *)

module type Type = sig module type T end

module Type = struct module type T = Type end

(** Define the absurd type *)

module type Absurd = functor (X : Type) -> X.T

module Absurd = struct module type T = Absurd end

(** Define the type of predicates *)

module Pred (A : Type) = struct
  module type T =
    functor (_ : A.T) -> Type
end

(** Define equality *)

module Eq (A : Type) (X : A.T) (Y : A.T) = struct
  module type T =
    functor (P : Pred(A).T) (_ : P(X).T) -> P(Y).T
end

module EqRefl (A : Type) (X : A.T) : Eq(A)(X)(X).T =
  functor (P : Pred(A).T) (PX : P(X).T) -> PX

module EqSymm (A : Type) (X : A.T) (Y : A.T)
              (EqXY : Eq(A)(X)(Y).T) : Eq(A)(Y)(X).T =
  EqXY(functor (E : A.T) -> Eq(A)(E)(X))(EqRefl(A)(X))

module EqTrans (A : Type) (X : A.T) (Y : A.T) (Z : A.T)
               (EqXY : Eq(A)(X)(Y).T) (EqYZ : Eq(A)(Y)(Z).T) : Eq(A)(X)(Z).T =
  EqYZ(Eq(A)(X))(EqXY)

(** Define types for relations and functions *)

module Rel (A : Type) (B : Type) = struct
  module type T = functor (_ : A.T) (_ : B.T) -> Type
end

module IsTotal (A : Type) (B : Type) (R : Rel(A)(B).T) = struct
  module type T =
    functor (X : A.T) (K : Type) (_ : functor (Y : B.T) (_ : R(X)(Y).T) -> K.T) -> K.T
end

module IsUnique (A : Type) (B : Type) (R : Rel(A)(B).T) = struct
  module type T =
    functor (X : A.T)
            (Y1 : B.T) (XtoY1 : R(X)(Y1).T)
            (Y2 : B.T) (XtoY2 : R(X)(Y2).T)
       -> Eq(B)(Y1)(Y2).T
end

module Func (A : Type) (B : Type) = struct
  module type T = sig
    module Maps : Rel(A)(B).T
    module Unique : IsUnique(A)(B)(Maps).T
    module Total : IsTotal(A)(B)(Maps).T
  end
end

(** Define identity functions *)
module Id (A : Type) = struct

  module Maps (X : A.T) (Y: A.T) = Eq(A)(X)(Y)

  module Unique (X : A.T)
                (Y1 : A.T) (XtoY1 : Maps(X)(Y1).T)
                (Y2 : A.T) (XtoY2 : Maps(X)(Y2).T) =
    EqTrans(A)(Y1)(X)(Y2)
           (EqSymm(A)(X)(Y1)(XtoY1))
           (XtoY2)

  module Total (X : A.T) (K : Type)
               (P : functor (Y : A.T) (XtoY : Maps(X)(Y).T) -> K.T) =
    P(X)(EqRefl(A)(X))

end

(** Define function composition *)

module Comp (A : Type) (B : Type) (C : Type)
            (F1 : Func(A)(B).T) (F2 : Func(B)(C).T) = struct

  module Maps (X : A.T) (Z : C.T) = struct
    module type T =
      functor (K : Type)
              (_ : functor (Y : B.T)
                           (XtoY : F1.Maps(X)(Y).T)
                           (YtoZ : F2.Maps(Y)(Z).T)
                   -> K.T)
        -> K.T
  end

  module Unique (X : A.T)
                (Z1 : C.T) (XtoZ1 : Maps(X)(Z1).T)
                (Z2 : C.T) (XtoZ2 : Maps(X)(Z2).T) =
      XtoZ1(Eq(C)(Z1)(Z2))(functor
          (Y1 : B.T)
          (XtoY1 : F1.Maps(X)(Y1).T)
          (Y1toZ1 : F2.Maps(Y1)(Z1).T) ->
            XtoZ2(Eq(C)(Z1)(Z2))(functor
              (Y2 : B.T)
              (XtoY2 : F1.Maps(X)(Y2).T)
              (Y2toZ2 : F2.Maps(Y2)(Z2).T) ->
                 F2.Unique
                   (Y2)
                   (Z1)(F1.Unique(X)(Y1)(XtoY1)(Y2)(XtoY2)
                          (functor (E : B.T) -> F2.Maps(E)(Z1))(Y1toZ1))
                   (Z2)(Y2toZ2)))

  module Total (X : A.T) =
      functor (K : Type) (P : functor (Z : C.T)
                                      (_ : Maps(X)(Z).T)
                              -> K.T) ->
        F1.Total(X)(K)(functor (Y : B.T)
                             (XtoY : F1.Maps(X)(Y).T) ->
        F2.Total(Y)(K)(functor (Z : C.T)
                             (YtoZ : F2.Maps(Y)(Z).T) ->
        P(Z)
         (functor (J : Type) (Q : functor (Y : B.T)
                                            (_ : F1.Maps(X)(Y).T)
                                            (_ : F2.Maps(Y)(Z).T)
                                  -> J.T) ->
            Q(Y)(XtoY)(YtoZ))))
end

(** Define transitivity for ordered sets *)

module Trans (S : Type) (Dom : Pred(S).T) (Ord : Rel(S)(S).T) = struct
  module type T =
    functor (X : S.T) (Y : S.T) (Z : S.T)
            (N : Ord(X)(Y).T) (M : Ord(Y)(Z).T) ->
      Ord(X)(Z).T
end

(** Define well-foundedness for ordered sets *)

module Base (S : Type) (Dom : Pred(S).T) (Ord : Rel(S)(S).T)
            (C : Pred(S).T) = struct
  module type T =
    functor (K : Type) (_ : functor (Z : S.T)
                                    (InDom : Dom(Z).T)
                                    (InC : C(Z).T)
                            -> K.T)
      -> K.T
end

module NoSmallest (S : Type) (Dom : Pred(S).T) (Ord : Rel(S)(S).T)
                  (C : Pred(S).T) = struct
  module type T =
    functor (X : S.T) (XInC : C(X).T) ->
      functor (K : Type) (_ : functor (Y : S.T)
                                      (YInC : C(Y).T)
                                      (IsSmaller : Ord(Y)(X).T)
                              -> K.T)
        -> K.T
end

module Chain (S : Type) (Dom : Pred(S).T) (Ord : Rel(S)(S).T) = struct
  module type T = sig
    module In : Pred(S).T
    module Base : Base(S)(Dom)(Ord)(In).T
    module NoSmallest : NoSmallest(S)(Dom)(Ord)(In).T
  end
end

module WellFounded (S : Type) (Dom : Pred(S).T) (Ord : Rel(S)(S).T) = struct
  module type T = functor (H : Chain(S)(Dom)(Ord).T) -> Absurd
end

(** Define an ordering on ordered sets based on embedding *)

module DomainPreserving (A : Type) (DomA : Pred(A).T) (OrdA : Rel(A)(A).T)
                        (B : Type) (DomB : Pred(B).T) (OrdB : Rel(B)(B).T)
                        (F : Func(A)(B).T) = struct
  module type T =
    functor (X : A.T) (Y : B.T) (_: F.Maps(X)(Y).T)
            (_ : DomA(X).T) -> DomB(Y).T
end

module Monotonic (A : Type) (DomA : Pred(A).T) (OrdA : Rel(A)(A).T)
                 (B : Type) (DomB : Pred(B).T) (OrdB : Rel(B)(B).T)
                 (F : Func(A)(B).T) = struct
  module type T =
    functor (X1 : A.T) (Y1 : B.T) (_ : F.Maps(X1)(Y1).T)
            (X2 : A.T) (Y2 : B.T) (_ : F.Maps(X2)(Y2).T)
            (_ : DomA(X1).T) (_ : DomA(X2).T)
            (_ : OrdA(X1)(X2).T) -> OrdB(Y1)(Y2).T
end

module Dominated (A : Type) (DomA : Pred(A).T) (OrdA : Rel(A)(A).T)
                 (B : Type) (DomB : Pred(B).T) (OrdB : Rel(B)(B).T)
                 (F : Func(A)(B).T) (E : B.T) = struct
  module type T =
    functor (X : A.T) (Y : B.T) (_ : F.Maps(X)(Y).T)
            (_ : DomA(X).T) -> OrdB(Y)(E).T
end

module Embedding (A : Type) (DomA : Pred(A).T) (OrdA : Rel(A)(A).T)
                 (B : Type) (DomB : Pred(B).T) (OrdB : Rel(B)(B).T)
                 (F : Func(A)(B).T) (E : B.T) = struct
  module type T = sig
    module InDom : DomB(E).T
    module DomPres : DomainPreserving(A)(DomA)(OrdA)(B)(DomB)(OrdB)(F).T
    module Mono : Monotonic(A)(DomA)(OrdA)(B)(DomB)(OrdB)(F).T
    module Dtd : Dominated(A)(DomA)(OrdA)(B)(DomB)(OrdB)(F)(E).T
  end
end

module EmbedOrd (A : Type) (DomA : Pred(A).T) (OrdA : Rel(A)(A).T)
                (B : Type) (DomB : Pred(B).T) (OrdB : Rel(B)(B).T) = struct
  module type T =
    functor (K : Type)
            (_ : functor (F : Func(A)(B).T)
                         (E : B.T)
                         (Emb : Embedding(A)(DomA)(OrdA)(B)(DomB)(OrdB)(F)(E).T)
                   -> K.T)
      -> K.T
end

(** Define U *)

module type OSPred =
  functor (S : Type) (Dom : Pred(S).T) (Order : Rel(S)(S).T) -> Type

module OSPred = struct
  module type T = OSPred
end

module type U = Pred(OSPred).T

module U = struct
  module type T = U
end

(** Define injection from ordered sets into U *)

module InjU (S : Type) (Dom : Pred(S).T) (Ord : Rel(S)(S).T) =
  functor (P : OSPred) -> P(S)(Dom)(Ord)

module InjUExt (A : Type) (DomA : Pred(A).T) (OrdA : Rel(A)(A).T)
              (B : Type) (DomB : Pred(B).T) (OrdB : Rel(B)(B).T)
              (EqI : Eq(U)(InjU(A)(DomA)(OrdA))(InjU(B)(DomB)(OrdB)).T)
              (P : OSPred) (PA : P(A)(DomA)(OrdA).T) : P(B)(DomB)(OrdB).T =
  EqI(functor (S : U) -> S(P))(PA)

(** Define the domain and ordering of U *)

module DomU (X : U) = struct
  module type T =
    functor (K : Type)
            (_ : functor (A : Type)
                         (DomA : Pred(A).T)
                         (OrdA : Rel(A)(A).T)
                         (TransA : Trans(A)(DomA)(OrdA).T)
                         (WellFoundedA : WellFounded(A)(DomA)(OrdA).T)
                         (EqXA : Eq(U)(X)(InjU(A)(DomA)(OrdA)).T)
                   -> K.T)
      -> K.T
end

module OrdU (X : U) (Y : U) = struct
  module type T =
    functor (K : Type)
            (_ : functor (A : Type)
                         (DomA : Pred(A).T)
                         (OrdA : Rel(A)(A).T)
                         (B : Type)
                         (DomB : Pred(B).T)
                         (OrdB : Rel(B)(B).T)
                         (EmbedAB : EmbedOrd(A)(DomA)(OrdA)(B)(DomB)(OrdB).T)
                         (EqXA : Eq(U)(X)(InjU(A)(DomA)(OrdA)).T)
                         (EqYB : Eq(U)(Y)(InjU(B)(DomB)(OrdB)).T)
                   -> K.T)
      -> K.T
end

(** Any ordered set in U is transitive and well-founded *)

module TransDomU (A : Type) (DomA : Pred(A).T) (OrdA : Rel(A)(A).T)
                 (InDom : DomU(InjU(A)(DomA)(OrdA)).T)
       : Trans(A)(DomA)(OrdA).T =
  InDom(Trans(A)(DomA)(OrdA))(functor
    (B : Type)
    (DomB : Pred(B).T)
    (OrdB : Rel(B)(B).T)
    (TransB : Trans(B)(DomB)(OrdB).T)
    (WellFoundedB : WellFounded(B)(DomB)(OrdB).T)
    (EqAB : Eq(U)(InjU(A)(DomA)(OrdA))(InjU(B)(DomB)(OrdB)).T) ->
      InjUExt(B)(DomB)(OrdB)(A)(DomA)(OrdA)
             (EqSymm(U)
                    (InjU(A)(DomA)(OrdA))
                    (InjU(B)(DomB)(OrdB))
                    (EqAB))
             (Trans)
             (TransB))

module WellFoundedDomU (A : Type) (DomA : Pred(A).T) (OrdA : Rel(A)(A).T)
                       (InDom : DomU(InjU(A)(DomA)(OrdA)).T)
       : WellFounded(A)(DomA)(OrdA).T =
  InDom(WellFounded(A)(DomA)(OrdA))(functor
    (B : Type)
    (DomB : Pred(B).T)
    (OrdB : Rel(B)(B).T)
    (TransB : Trans(B)(DomB)(OrdB).T)
    (WellFoundedB : WellFounded(B)(DomB)(OrdB).T)
    (EqAB : Eq(U)(InjU(A)(DomA)(OrdA))(InjU(B)(DomB)(OrdB)).T) ->
      InjUExt(B)(DomB)(OrdB)(A)(DomA)(OrdA)
             (EqSymm(U)
                    (InjU(A)(DomA)(OrdA))
                    (InjU(B)(DomB)(OrdB))
                    (EqAB))
             (WellFounded)
             (WellFoundedB))

(** Embeddings are transitive across EmbedOrd *)

module EmbedOrdTransEmbedding (A : Type) (DomA : Pred(A).T) (OrdA : Rel(A)(A).T)
                              (B : Type) (DomB : Pred(B).T) (OrdB : Rel(B)(B).T)
                              (C : Type) (DomC : Pred(C).T) (OrdC : Rel(C)(C).T)
                              (EmbedOrdAB : EmbedOrd(A)(DomA)(OrdA)(B)(DomB)(OrdB).T)
                              (F_BC : Func(B)(C).T)
                              (E_C : C.T)
                              (Emb_BC : Embedding(B)(DomB)(OrdB)(C)(DomC)(OrdC)(F_BC)(E_C).T) =
  functor (K : Type) (P : functor (F : Func(A)(C).T)
                                  (E : C.T)
                                  (Emb : Embedding(A)(DomA)(OrdA)(C)(DomC)(OrdC)(F)(E).T)
                                  (IsSmaller : OrdC(E)(E_C).T)
                          -> K.T) ->
  EmbedOrdAB(K)(functor (F_AB : Func(A)(B).T)
                        (E_B : B.T)
                        (Emb_AB : Embedding(A)(DomA)(OrdA)(B)(DomB)(OrdB)(F_AB)(E_B).T) ->
  F_BC.Total(E_B)(K)(functor (E : C.T)
                             (E_BtoE : F_BC.Maps(E_B)(E).T) ->
  P(Comp(A)(B)(C)(F_AB)(F_BC))
   (E)
   (struct
      module InDom : DomC(E).T =
        Emb_BC.DomPres(E_B)(E)(E_BtoE)(Emb_AB.InDom)

      module DomPres (X : A.T) (Z : C.T)
                     (XtoZ : Comp(A)(B)(C)(F_AB)(F_BC).Maps(X)(Z).T)
                     (InDom : DomA(X).T) : DomC(Z).T =
        XtoZ(DomC(Z))(functor
          (Y : B.T)
          (XtoY : F_AB.Maps(X)(Y).T)
          (YtoZ : F_BC.Maps(Y)(Z).T) ->
        Emb_BC.DomPres(Y)(Z)(YtoZ)(Emb_AB.DomPres(X)(Y)(XtoY)(InDom)))

      module Mono (X1 : A.T) (Z1 : C.T) (X1toZ1 : Comp(A)(B)(C)(F_AB)(F_BC).Maps(X1)(Z1).T)
                  (X2 : A.T) (Z2 : C.T) (X2toZ2 : Comp(A)(B)(C)(F_AB)(F_BC).Maps(X2)(Z2).T)
                  (X1InDom : DomA(X1).T) (X2InDom : DomA(X2).T)
                  (Ordered : OrdA(X1)(X2).T) : OrdC(Z1)(Z2).T =
        X1toZ1(OrdC(Z1)(Z2))(functor
          (Y1 : B.T)
          (X1toY1 : F_AB.Maps(X1)(Y1).T)
          (Y1toZ1 : F_BC.Maps(Y1)(Z1).T) ->
        X2toZ2(OrdC(Z1)(Z2))(functor
          (Y2 : B.T)
          (X2toY2 : F_AB.Maps(X2)(Y2).T)
          (Y2toZ2 : F_BC.Maps(Y2)(Z2).T) ->
        Emb_BC.Mono(Y1)(Z1)(Y1toZ1)
                   (Y2)(Z2)(Y2toZ2)
                   (Emb_AB.DomPres(X1)(Y1)(X1toY1)(X1InDom))
                   (Emb_AB.DomPres(X2)(Y2)(X2toY2)(X2InDom))
                   (Emb_AB.Mono(X1)(Y1)(X1toY1)
                               (X2)(Y2)(X2toY2)
                               (X1InDom)(X2InDom)(Ordered))))

      module Dtd (X : A.T) (Z : C.T) (XtoZ : Comp(A)(B)(C)(F_AB)(F_BC).Maps(X)(Z).T)
                 (XInDom : DomA(X).T) : OrdC(Z)(E).T =
        XtoZ(OrdC(Z)(E))(functor
          (Y : B.T)
          (XtoY : F_AB.Maps(X)(Y).T)
          (YtoZ : F_BC.Maps(Y)(Z).T) ->
        Emb_BC.Mono(Y)(Z)(YtoZ)
                   (E_B)(E)(E_BtoE)
                   (Emb_AB.DomPres(X)(Y)(XtoY)(XInDom))
                   (Emb_AB.InDom)
                   (Emb_AB.Dtd(X)(Y)(XtoY)(XInDom)))
   end)
   (Emb_BC.Dtd(E_B)(E)(E_BtoE)(Emb_AB.InDom))))

(** EmbedOrd is transitive *)

module TransEmbedOrd (A : Type) (DomA : Pred(A).T) (OrdA : Rel(A)(A).T)
                     (B : Type) (DomB : Pred(B).T) (OrdB : Rel(B)(B).T)
                     (C : Type) (DomC : Pred(C).T) (OrdC : Rel(C)(C).T)
                     (EmbedOrdAB : EmbedOrd(A)(DomA)(OrdA)(B)(DomB)(OrdB).T)
                     (EmbedOrdBC : EmbedOrd(B)(DomB)(OrdB)(C)(DomC)(OrdC).T)
       : EmbedOrd(A)(DomA)(OrdA)(C)(DomC)(OrdC).T =
  functor (K : Type) (P : functor (F : Func(A)(C).T)
                                  (E : C.T)
                                  (Emb : Embedding(A)(DomA)(OrdA)
                                                  (C)(DomC)(OrdC)
                                                  (F)(E).T)
                                  -> K.T) ->
    EmbedOrdBC(K)(functor (F_BC : Func(B)(C).T)
                          (E_C : C.T)
                          (Emb_BC : Embedding(B)(DomB)(OrdB)(C)(DomC)(OrdC)(F_BC)(E_C).T) ->
    EmbedOrdTransEmbedding(A)(DomA)(OrdA)(B)(DomB)(OrdB)(C)(DomC)(OrdC)
                          (EmbedOrdAB)(F_BC)(E_C)(Emb_BC)
                          (K)(functor (F : Func(A)(C).T)
                                      (E : C.T)
                                      (Emb : Embedding(A)(DomA)(OrdA)(C)(DomC)(OrdC)(F)(E).T)
                                      (_ : OrdC(E)(E_C).T) ->
    P(F)(E)(Emb)))

(* U is transitive *)

module TransU (X : U.T) (Y : U.T) (Z : U.T)
              (N : OrdU(X)(Y).T) (M : OrdU(Y)(Z).T) =
  functor (K : Type) (P : functor (A : Type)
                                  (DomA : Pred(A).T)
                                  (OrdA : Rel(A)(A).T)
                                  (D : Type)
                                  (DomD : Pred(D).T)
                                  (OrdD : Rel(D)(D).T)
                                  (EmbedAD : EmbedOrd(A)(DomA)(OrdA)(D)(DomD)(OrdD).T)
                                  (EqXA : Eq(U)(X)(InjU(A)(DomA)(OrdA)).T)
                                  (EqZD : Eq(U)(Z)(InjU(D)(DomD)(OrdD)).T) -> K.T) ->
    N(K)(functor (A : Type)
                 (DomA : Pred(A).T)
                 (OrdA : Rel(A)(A).T)
                 (B : Type)
                 (DomB : Pred(B).T)
                 (OrdB : Rel(B)(B).T)
                 (EmbedAB : EmbedOrd(A)(DomA)(OrdA)(B)(DomB)(OrdB).T)
                 (EqXA : Eq(U)(X)(InjU(A)(DomA)(OrdA)).T)
                 (EqYB : Eq(U)(Y)(InjU(B)(DomB)(OrdB)).T) ->
    M(K)(functor (C : Type)
                 (DomC : Pred(C).T)
                 (OrdC : Rel(C)(C).T)
                 (D : Type)
                 (DomD : Pred(D).T)
                 (OrdD : Rel(D)(D).T)
                 (EmbedCD : EmbedOrd(C)(DomC)(OrdC)(D)(DomD)(OrdD).T)
                 (EqYC : Eq(U)(Y)(InjU(C)(DomC)(OrdC)).T)
                 (EqZD : Eq(U)(Z)(InjU(D)(DomD)(OrdD)).T) ->
     P(A)(DomA)(OrdA)(D)(DomD)(OrdD)
      (TransEmbedOrd(A)(DomA)(OrdA)
                    (B)(DomB)(OrdB)
                    (D)(DomD)(OrdD)
                    (EmbedAB)
                    (InjUExt(C)(DomC)(OrdC)(B)(DomB)(OrdB)
                            (EqTrans(U)(InjU(C)(DomC)(OrdC))(Y)(InjU(B)(DomB)(OrdB))
                                    (EqSymm(U)(Y)(InjU(C)(DomC)(OrdC))(EqYC))(EqYB))
                            (functor (S : Type) (Dom : Pred(S).T) (Order : Rel(S)(S).T) ->
                                     EmbedOrd(S)(Dom)(Order)(D)(DomD)(OrdD))
                            (EmbedCD)))
      (EqXA)(EqZD)))

(* U is well-founded *)

module WellFoundedU : WellFounded(U)(DomU)(OrdU).T =
  functor (M : Chain(U)(DomU)(OrdU).T) ->
  M.Base(Absurd)(functor (ZU : U.T)
                         (ZInDomU : DomU(ZU).T)
                         (ZInM : M.In(ZU).T) ->
  ZInDomU(Absurd)(functor (Z : Type)
                         (DomZ : Pred(Z).T)
                         (OrdZ : Rel(Z)(Z).T)
                         (TransZ : Trans(Z)(DomZ)(OrdZ).T)
                         (WellFoundedZ : WellFounded(Z)(DomZ)(OrdZ).T)
                         (EqInjZ : Eq(U)(ZU)(InjU(Z)(DomZ)(OrdZ)).T) ->
  WellFoundedDomU(Z)(DomZ)(OrdZ)(EqInjZ(DomU)(ZInDomU))
  (struct
     module InN (X : Type) (DomX : Pred(X).T) (OrdX : Rel(X)(X).T) (E : X.T) = struct
       module type T =
         functor (K : Type) (_ : functor (Y : Type)
                                         (DomY : Pred(Y).T)
                                         (OrdY : Rel(Y)(Y).T)
                                         (F : Func(Y)(X).T)
                                         (_ : M.In(InjU(Y)(DomY)(OrdY)).T)
                                         (_ : Embedding(Y)(DomY)(OrdY)(X)(DomX)(OrdX)(F)(E).T)
                                 -> K.T)
           -> K.T
     end
     module In = InN(Z)(DomZ)(OrdZ)

     module Base =
       functor (K : Type)
               (P : functor (E : Z.T) (_ : DomZ(E).T) (_ : In(E).T) -> K.T) ->
         M.NoSmallest(ZU)(ZInM)(K)(functor (YU : U.T)
                                           (YInM : M.In(YU).T)
                                           (YOrdZ : OrdU(YU)(ZU).T) ->
         YOrdZ(K)(functor (Y : Type)
                          (DomY : Pred(Y).T)
                          (OrdY : Rel(Y)(Y).T)
                          (Z' : Type)
                          (DomZ' : Pred(Z').T)
                          (OrdZ' : Rel(Z')(Z').T)
                          (EmbedYZ' : EmbedOrd(Y)(DomY)(OrdY)(Z')(DomZ')(OrdZ').T)
                          (EqInjY : Eq(U)(YU)(InjU(Y)(DomY)(OrdY)).T)
                          (EqInjZ' : Eq(U)(ZU)(InjU(Z')(DomZ')(OrdZ')).T) ->
         EmbedYZ'(K)(functor (F : Func(Y)(Z').T)
                             (E : Z'.T)
                             (Emb : Embedding(Y)(DomY)(OrdY)(Z')(DomZ')(OrdZ')(F)(E).T) ->
         InjUExt(Z')(DomZ')(OrdZ')(Z)(DomZ)(OrdZ)
                (EqTrans(U)(InjU(Z')(DomZ')(OrdZ'))(ZU)(InjU(Z)(DomZ)(OrdZ))
                        (EqSymm(U)(ZU)(InjU(Z')(DomZ')(OrdZ'))(EqInjZ'))(EqInjZ))
                (functor (X : Type) (DomX : Pred(X).T) (OrdX : Rel(X)(X).T) -> struct
                   module type T =
                     functor (_ : functor (E : X.T)
                                          (_ : DomX(E).T)
                                          (_ : InN(X)(DomX)(OrdX)(E).T)
                                  -> K.T)
                     -> K.T
                 end)
                (functor (Q : functor (E : Z'.T)
                                      (_ : DomZ'(E).T)
                                      (_ : InN(Z')(DomZ')(OrdZ')(E).T)
                              -> K.T) ->
                   Q(E)
                    (Emb.InDom)
                    (functor (K : Type)
                             (R : functor (Y : Type) (DomY : Pred(Y).T) (OrdY : Rel(Y)(Y).T)
                                          (F : Func(Y)(Z').T)
                                          (_ : M.In(InjU(Y)(DomY)(OrdY)).T)
                                          (_ : Embedding(Y)(DomY)(OrdY)(Z')(DomZ')(OrdZ')(F)(E).T)
                                  -> K.T) ->
                       R(Y)(DomY)(OrdY)(F)(EqInjY(M.In)(YInM))(Emb)))
                (P))))

     module NoSmallest =
       functor (A : Z.T) (CInN : In(A).T) ->
         functor (K : Type) (P : functor (B : Z.T)
                                         (_ : In(B).T)
                                         (_ : OrdZ(B)(A).T)
                              -> K.T) ->
           CInN(K)(functor (Y : Type)
                           (DomY : Pred(Y).T)
                           (OrdY : Rel(Y)(Y).T)
                           (F : Func(Y)(Z).T)
                           (YInM : M.In(InjU(Y)(DomY)(OrdY)).T)
                           (Emb : Embedding(Y)(DomY)(OrdY)(Z)(DomZ)(OrdZ)(F)(A).T) ->
           M.NoSmallest(InjU(Y)(DomY)(OrdY))(YInM)(K)
                       (functor (XU : U.T)
                                (XInM : M.In(XU).T)
                                (XOrdY : OrdU(XU)(InjU(Y)(DomY)(OrdY)).T) ->
           XOrdY(K)(functor (X : Type)
                            (DomX : Pred(X).T)
                            (OrdX : Rel(X)(X).T)
                            (Y' : Type)
                            (DomY' : Pred(Y').T)
                            (OrdY' : Rel(Y')(Y').T)
                            (EmbedXY' : EmbedOrd(X)(DomX)(OrdX)(Y')(DomY')(OrdY').T)
                            (EqInjX : Eq(U)(XU)(InjU(X)(DomX)(OrdX)).T)
                            (EqInjYY' : Eq(U)(InjU(Y)(DomY)(OrdY))(InjU(Y')(DomY')(OrdY')).T) ->
           EmbedOrdTransEmbedding(X)(DomX)(OrdX)(Y)(DomY)(OrdY)(Z)(DomZ)(OrdZ)
                                 (InjUExt(Y')(DomY')(OrdY')(Y)(DomY)(OrdY)
                                         (EqSymm(U)(InjU(Y)(DomY)(OrdY))(InjU(Y')(DomY')(OrdY'))(EqInjYY'))
                                         (EmbedOrd(X)(DomX)(OrdX))(EmbedXY'))
                                 (F)(A)(Emb)
                                 (K)(functor (G : Func(X)(Z).T)
                                             (B : Z.T)
                                             (Emb : Embedding(X)(DomX)(OrdX)(Z)(DomZ)(OrdZ)(G)(B).T)
                                             (IsSmaller : OrdZ(B)(A).T) ->
           P(B)
            (functor (K : Type) (Q : functor (X : Type)
                                             (DomX : Pred(X).T)
                                             (OrdX : Rel(X)(X).T)
                                             (G : Func(X)(Z).T)
                                             (_ : M.In(InjU(X)(DomX)(OrdX)).T)
                                             (_ : Embedding(X)(DomX)(OrdX)(Z)(DomZ)(OrdZ)(G)(B).T)
                                     -> K.T) ->
             Q(X)(DomX)(OrdX)(G)(EqInjX(M.In)(XInM))(Emb))
            (IsSmaller)))))

   end)))

(* U is in U *)

module UInU : DomU(InjU(U)(DomU)(OrdU)).T =
  functor (K : Type) (P : functor (A : Type)
                                  (DomA : Pred(A).T)
                                  (OrdA : Rel(A)(A).T)
                                  (TransA : Trans(A)(DomA)(OrdA).T)
                                  (WellFoundedA : WellFounded(A)(DomA)(OrdA).T)
                                  (EqUA : Eq(U)(InjU(U)(DomU)(OrdU))(InjU(A)(DomA)(OrdA)).T)
                          -> K.T) ->
    P(U)(DomU)(OrdU)(TransU)(WellFoundedU)(EqRefl(U)(InjU(U)(DomU)(OrdU)))

(* Define the intial segment domain of an ordered set and element *)

module InitialSegmentDom (S : Type) (Dom : Pred(S).T) (Ord : Rel(S)(S).T) (A : S.T) =
  functor (X : S.T) -> struct
      module type T = sig
        module InDom : Dom(X).T
        module IsSmaller : Ord(X)(A).T
      end
  end

(* If A is in U and x is in A then the initial segment of A and x is in U *)

module InitialSegmentsInU (A : Type) (DomA : Pred(A).T) (OrdA : Rel(A)(A).T) (X : A.T)
                          (AInU : DomU(InjU(A)(DomA)(OrdA)).T) (XInA : DomA(X).T)
       : DomU(InjU(A)(InitialSegmentDom(A)(DomA)(OrdA)(X))(OrdA)).T =
    functor (K : Type) (P : functor (B : Type)
                                    (DomB : Pred(B).T)
                                    (OrdB : Rel(B)(B).T)
                                    (TransB : Trans(B)(DomB)(OrdB).T)
                                    (WellFoundedB : WellFounded(B)(DomB)(OrdB).T)
                                    (EqInjAB : Eq(U)(InjU(A)(InitialSegmentDom(A)(DomA)(OrdA)(X))(OrdA))
                                              (InjU(B)(DomB)(OrdB)).T)
                            -> K.T) ->
    AInU(K)(functor (A' : Type)
                    (DomA' : Pred(A').T)
                    (OrdA' : Rel(A')(A').T)
                    (TransA' : Trans(A')(DomA')(OrdA').T)
                    (WellFoundedA' : WellFounded(A')(DomA')(OrdA').T)
                    (EqInjAA' : Eq(U)(InjU(A)(DomA)(OrdA))(InjU(A')(DomA')(OrdA')).T) ->
    P(A)
     (InitialSegmentDom(A)(DomA)(OrdA)(X))
     (OrdA)
     (InjUExt(A')(DomA')(OrdA')(A)(DomA)(OrdA)
             (EqSymm(U)(InjU(A)(DomA)(OrdA))(InjU(A')(DomA')(OrdA'))(EqInjAA'))
             (Trans)(TransA'))
     (functor (M : Chain(A)(InitialSegmentDom(A)(DomA)(OrdA)(X))(OrdA).T) ->
        InjUExt(A')(DomA')(OrdA')(A)(DomA)(OrdA)
               (EqSymm(U)(InjU(A)(DomA)(OrdA))(InjU(A')(DomA')(OrdA'))(EqInjAA'))
               (WellFounded)(WellFoundedA')
               (struct
                   module In = M.In
                   module Base =
                     functor (K : Type) (P : functor (Y : A.T)
                                                     (InDomA : DomA(Y).T)
                                                     (InN : In(Y).T)
                                             -> K.T) ->
                     M.Base(K)(functor (Y : A.T)
                                       (InSeg : InitialSegmentDom(A)(DomA)(OrdA)(X)(Y).T)
                                       (InM : M.In(Y).T) ->
                     P(Y)(InSeg.InDom)(InM))
                   module NoSmallest = M.NoSmallest
                 end)
     )
     (EqRefl(U)(InjU(A)(InitialSegmentDom(A)(DomA)(OrdA)(X))(OrdA))))

(* Given a transitive ordered set S and elements A and B in S such that A < B
   then the initial segment of A is less than the initial segment of B by
   EmbedOrd *)
module OrdInitialSegmentsEmbed (S : Type) (DomS : Pred(S).T) (OrdS : Rel(S)(S).T)
                               (TransS : Trans(S)(DomS)(OrdS).T)
                               (A : S.T) (AInS : DomS(A).T)
                               (B : S.T) (BInS : DomS(B).T)
                               (ASmallerB : OrdS(A)(B).T)
       : EmbedOrd(S)(InitialSegmentDom(S)(DomS)(OrdS)(A))(OrdS)
                 (S)(InitialSegmentDom(S)(DomS)(OrdS)(B))(OrdS).T =
  functor (K : Type) (P : functor (F : Func(S)(S).T)
                                  (E : S.T)
                                  (Emb : Embedding(S)(InitialSegmentDom(S)(DomS)(OrdS)(A))(OrdS)
                                                  (S)(InitialSegmentDom(S)(DomS)(OrdS)(B))(OrdS)
                                                  (F)(E).T)
                          -> K.T) ->
    P(Id(S))(A)
     (struct
         module InDom = struct
             module InDom = AInS
             module IsSmaller = ASmallerB
           end

         module DomPres (X : S.T) (Y : S.T) (XtoY: Eq(S)(X)(Y).T)
                        (XinSegA : InitialSegmentDom(S)(DomS)(OrdS)(A)(X).T) = struct
             module InDom = XtoY(DomS)(XinSegA.InDom)
             module IsSmaller = TransS(Y)(A)(B)
                                      (XtoY(functor (E : S.T) -> OrdS(E)(A))(XinSegA.IsSmaller))
                                      (ASmallerB)
           end

         module Mono (X1 : S.T) (Y1 : S.T) (X1toY1 : Eq(S)(X1)(Y1).T)
                     (X2 : S.T) (Y2 : S.T) (X2toY2 : Eq(S)(X2)(Y2).T)
                     (_ : InitialSegmentDom(S)(DomS)(OrdS)(A)(X1).T)
                     (_ : InitialSegmentDom(S)(DomS)(OrdS)(A)(X2).T)
                     (X1SmallerX2 : OrdS(X1)(X2).T) =
           X1toY1(functor (E : S.T) -> OrdS(E)(Y2))
                 (X2toY2(functor (E : S.T) -> OrdS(X1)(E))
                        (X1SmallerX2))

         module Dtd (X : S.T) (Y : S.T) (XtoY : Eq(S)(X)(Y).T)
                    (XinSegA : InitialSegmentDom(S)(DomS)(OrdS)(A)(X).T) =
           XtoY(functor (E : S.T) -> OrdS(E)(A))(XinSegA.IsSmaller)
       end)

(* Given a ordered set S and element A in S then the initial segment
   of A is less than S by EmbedOrd *)
module InitialSegmentEmbeds (S : Type) (DomS : Pred(S).T) (OrdS : Rel(S)(S).T)
                              (A : S.T) (AInS : DomS(A).T)
       : EmbedOrd(S)(InitialSegmentDom(S)(DomS)(OrdS)(A))(OrdS)
                 (S)(DomS)(OrdS).T =
  functor (K : Type) (P : functor (F : Func(S)(S).T)
                                  (E : S.T)
                                  (Emb : Embedding(S)(InitialSegmentDom(S)(DomS)(OrdS)(A))(OrdS)
                                                  (S)(DomS)(OrdS)(F)(E).T)
                          -> K.T) ->
    P(Id(S))(A)
     (struct
        module InDom = AInS

        module DomPres (X : S.T) (Y : S.T) (XtoY: Eq(S)(X)(Y).T)
                       (XinSegA : InitialSegmentDom(S)(DomS)(OrdS)(A)(X).T) =
          XtoY(DomS)(XinSegA.InDom)

        module Mono (X1 : S.T) (Y1 : S.T) (X1toY1 : Eq(S)(X1)(Y1).T)
                    (X2 : S.T) (Y2 : S.T) (X2toY2 : Eq(S)(X2)(Y2).T)
                    (_ : InitialSegmentDom(S)(DomS)(OrdS)(A)(X1).T)
                    (_ : InitialSegmentDom(S)(DomS)(OrdS)(A)(X2).T)
                    (X1SmallerX2 : OrdS(X1)(X2).T) =
          X1toY1(functor (E : S.T) -> OrdS(E)(Y2))
                (X2toY2(functor (E : S.T) -> OrdS(X1)(E))
                       (X1SmallerX2))

        module Dtd (X : S.T) (Y : S.T) (XtoY : Eq(S)(X)(Y).T)
                   (XinSegA : InitialSegmentDom(S)(DomS)(OrdS)(A)(X).T) =
            XtoY(functor (E : S.T) -> OrdS(E)(A))(XinSegA.IsSmaller)
       end)

(* If A is in U then A < U *)

module EmbedOrdAInUAndU (A : Type) (DomA : Pred(A).T) (OrdA : Rel(A)(A).T)
                        (AInU : DomU(InjU(A)(DomA)(OrdA)).T)
       : EmbedOrd(A)(DomA)(OrdA)(U)(DomU)(OrdU).T =
    functor (K : Type)
            (P : functor (F : Func(A)(U).T)
                         (E : U.T)
                         (Emb : Embedding(A)(DomA)(OrdA)(U)(DomU)(OrdU)(F)(E).T)
                   -> K.T) ->
      P(struct
           module Maps (X : A.T) (Y : U.T) =
             Eq(U)(InjU(A)(InitialSegmentDom(A)(DomA)(OrdA)(X))(OrdA))(Y)

           module Unique (X : A.T)
                         (Y1 : U.T) (XtoY1 : Maps(X)(Y1).T)
                         (Y2 : U.T) (XtoY2 : Maps(X)(Y2).T) =
                  EqTrans(U)(Y1)(InjU(A)(InitialSegmentDom(A)(DomA)(OrdA)(X))(OrdA))(Y2)
                         (EqSymm(U)(InjU(A)(InitialSegmentDom(A)(DomA)(OrdA)(X))(OrdA))(Y1)(XtoY1))
                         (XtoY2)

           module Total (X : A.T) (L : Type) (Q : functor (Y : U.T) (XtoY : Maps(X)(Y).T) -> L.T) =
             Q(InjU(A)(InitialSegmentDom(A)(DomA)(OrdA)(X))(OrdA))
              (EqRefl(U)(InjU(A)(InitialSegmentDom(A)(DomA)(OrdA)(X))(OrdA)))
         end)
       (InjU(A)(DomA)(OrdA))
       (struct
           module InDom = AInU

           module DomPres (X : A.T) (Y : U.T)
                          (XtoY : Eq(U)(InjU(A)(InitialSegmentDom(A)(DomA)(OrdA)(X))(OrdA))(Y).T)
                          (XInA : DomA(X).T) =
             XtoY(DomU)(InitialSegmentsInU(A)(DomA)(OrdA)(X)(AInU)(XInA))

           module Mono (X1 : A.T) (Y1 : U.T)
                       (X1toY1 : Eq(U)(InjU(A)(InitialSegmentDom(A)(DomA)(OrdA)(X1))(OrdA))(Y1).T)
                       (X2 : A.T) (Y2 : U.T)
                       (X2toY2 : Eq(U)(InjU(A)(InitialSegmentDom(A)(DomA)(OrdA)(X2))(OrdA))(Y2).T)
                       (X1InA : DomA(X1).T) (X2InA : DomA(X2).T)
                       (OrdAX1andX2 : OrdA(X1)(X2).T) =
             functor (L : Type)
                     (Q : functor (B : Type)
                                  (DomB : Pred(B).T)
                                  (OrdB : Rel(B)(B).T)
                                  (C : Type)
                                  (DomC : Pred(C).T)
                                  (OrdC : Rel(C)(C).T)
                                  (EmbedBC : EmbedOrd(B)(DomB)(OrdB)(C)(DomC)(OrdC).T)
                                  (EqY1B : Eq(U)(Y1)(InjU(B)(DomB)(OrdB)).T)
                                  (EqY2C : Eq(U)(Y2)(InjU(C)(DomC)(OrdC)).T)
                          -> L.T) ->
             Q(A)(InitialSegmentDom(A)(DomA)(OrdA)(X1))(OrdA)
              (A)(InitialSegmentDom(A)(DomA)(OrdA)(X2))(OrdA)
              (OrdInitialSegmentsEmbed(A)(DomA)(OrdA)
                                     (TransDomU(A)(DomA)(OrdA)(AInU))
                                     (X1) (X1InA)
                                     (X2) (X2InA)
                                     (OrdAX1andX2))
              (EqSymm(U)(InjU(A)(InitialSegmentDom(A)(DomA)(OrdA)(X1))(OrdA))(Y1)
                     (X1toY1))
              (EqSymm(U)(InjU(A)(InitialSegmentDom(A)(DomA)(OrdA)(X2))(OrdA))(Y2)
                     (X2toY2))

           module Dtd (X : A.T) (Y : U.T)
                      (XtoY : Eq(U)(InjU(A)(InitialSegmentDom(A)(DomA)(OrdA)(X))(OrdA))(Y).T)
                      (XInA : DomA(X).T) =
             functor (L : Type)
                     (Q : functor (B : Type)
                                  (DomB : Pred(B).T)
                                  (OrdB : Rel(B)(B).T)
                                  (C : Type)
                                  (DomC : Pred(C).T)
                                  (OrdC : Rel(C)(C).T)
                                  (EmbedBC : EmbedOrd(B)(DomB)(OrdB)(C)(DomC)(OrdC).T)
                                  (EqYB : Eq(U)(Y)(InjU(B)(DomB)(OrdB)).T)
                                  (EqAC : Eq(U)(InjU(A)(DomA)(OrdA))(InjU(C)(DomC)(OrdC)).T)
                          -> L.T) ->
             Q(A)(InitialSegmentDom(A)(DomA)(OrdA)(X))(OrdA)
              (A)(DomA)(OrdA)
              (InitialSegmentEmbeds(A)(DomA)(OrdA)(X)(XInA))
              (EqSymm(U)(InjU(A)(InitialSegmentDom(A)(DomA)(OrdA)(X))(OrdA))(Y)
                     (XtoY))
              (EqRefl(U)(InjU(A)(DomA)(OrdA)))
         end)

module USmallerU : OrdU(InjU(U)(DomU)(OrdU))(InjU(U)(DomU)(OrdU)).T =
  functor (K : Type)
          (P : functor (A : Type)
                       (DomA : Pred(A).T)
                       (OrdA : Rel(A)(A).T)
                       (B : Type)
                       (DomB : Pred(B).T)
                       (OrdB : Rel(B)(B).T)
                       (EmbedAB : EmbedOrd(A)(DomA)(OrdA)(B)(DomB)(OrdB).T)
                       (EqXA : Eq(U)(InjU(U)(DomU)(OrdU))(InjU(A)(DomA)(OrdA)).T)
                       (EqYB : Eq(U)(InjU(U)(DomU)(OrdU))(InjU(B)(DomB)(OrdB)).T)
               -> K.T) ->
  P(U)(DomU)(OrdU)
   (U)(DomU)(OrdU)
   (EmbedOrdAInUAndU(U)(DomU)(OrdU)(UInU))
   (EqRefl(U)(InjU(U)(DomU)(OrdU)))
   (EqRefl(U)(InjU(U)(DomU)(OrdU)))

module UChain : Chain(U)(DomU)(OrdU).T = struct
  module In (S : U.T) = Eq(U)(InjU(U)(DomU)(OrdU))(S)

  module Base (K : Type) (P : functor (Z : U.T)
                                      (InDom : DomU(Z).T)
                                      (InZ : In(Z).T)
                              -> K.T) =
    P(InjU(U)(DomU)(OrdU))
     (UInU)
     (EqRefl(U)(InjU(U)(DomU)(OrdU)))

  module NoSmallest (X :U.T) (XInC : In(X).T)
                    (K : Type) (P : functor (Y : U.T)
                                            (YInC : In(Y).T)
                                            (IsSmaller : OrdU(Y)(X).T)
                                    -> K.T) =
    P(InjU(U)(DomU)(OrdU))
     (EqRefl(U)(InjU(U)(DomU)(OrdU)))
     (XInC(OrdU(InjU(U)(DomU)(OrdU)))(USmallerU))
end

module Paradox : Absurd = WellFoundedU(UChain)
