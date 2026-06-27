{-# OPTIONS --rewriting #-}

module IntrpWellDefCases.LeftImpLTensorR1 where

open import IntrpWellDefCases.Base

⊗R-assoc-eqh : ∀ {Δ₀ Δ₁ Δ₂ DG DH DK}
  {hG : Δ₀ ⊢ DG} {hH : Δ₁ ⊢ DH} {hK : Δ₂ ⊢ DK}
  → cut [] (⊗R (⊗R hG hH) hK)
      (⊗L {[]} (⊗L {[]} (⊗R ax (⊗R ax ax)))) refl
      ≗ ⊗R hG (⊗R hH hK)
⊗R-assoc-eqh = refl

⇐L⊗R₁-assoc~ : ∀ {Γ₀ Γ₁ Δ₀ Δ₁ Δ₂ Λ A B A' B'}
  → (G : MIP Γ₁ Δ₀ [] A)
  → (H : MIP (Γ₀ ++ B ∷ []) Δ₁ [] A')
  → (K : MIP [] Δ₂ Λ B')
  → ⇐L~⊗' {Γ₀ = Γ₀} {Γ₁ = Γ₁} {Δ₀ = Δ₀} {Δ₁ = Δ₁ ++ Δ₂} {Λ = Λ}
      G (⊗R~' H K)
      ~ ⊗R~' {Γ = Γ₀ ++ B ⇐ A ∷ Γ₁} {Δ₀ = Δ₀ ++ Δ₁} {Δ₁ = Δ₂} {Λ = Λ}
          (⇐L~⊗' {Γ₀ = Γ₀} {Γ₁ = Γ₁} {Δ₀ = Δ₀} {Δ₁ = Δ₁} {Λ = []} G H) K
⇐L⊗R₁-assoc~ {Γ₀} {Γ₁} {Δ₀} {Δ₁} {Δ₂} {Λ = Λ} {A} {B}
  (intrp DG gG hG) (intrp DH gH hH) (intrp DK gK hK) =
  let Γo = Γ₀ ++ B ⇐ A ∷ Γ₁
      body : Γo ++ DG ∷ DH ⊗ DK ∷ Λ ⊢ _
      body =
        ⇐L {Γ = Γ₀} {Δ = Γ₁ ++ DG ∷ []} {Λ = DH ⊗ DK ∷ Λ}
          gG
          (⊗L {Γ₀ ++ B ∷ []} {Λ} {DH} {DK} (⊗R gH gK))
      q : DH ∷ DK ∷ [] ⊢ DH ⊗ DK
      q = ⊗R ax ax
      r : DG ∷ DH ∷ DK ∷ [] ⊢ DG ⊗ (DH ⊗ DK)
      r = ⊗R ax q
      s : DG ⊗ DH ∷ DK ∷ [] ⊢ DG ⊗ (DH ⊗ DK)
      s = ⊗L {[]} r
      t : (DG ⊗ DH) ⊗ DK ∷ [] ⊢ DG ⊗ (DH ⊗ DK)
      t = ⊗L {[]} s
      eqInner : ⇐L gG (⊗R gH gK) ≗ cut (Γo ++ DG ∷ []) q body refl
      eqInner =
        (⇐L refl
          ((~ cutaxA-left (Γ₀ ++ B ∷ []) (⊗R gH gK) refl)
           ∘
           (cut-cong₂ (Γ₀ ++ B ∷ []) refl
             (~ cutaxA-left (Γ₀ ++ B ∷ DH ∷ [])
               (⊗R gH gK) refl)
           ∘
           ≡to≗ (cut⊗R⊗Lcases++ (Γ₀ ++ B ∷ []) Λ
             {f = ax} {g = ax} {h = ⊗R gH gK}))))
        ∘
        (~ (≡to≗ (cut⇐L-cases++-comm₁ Γ₀
          {Γ₁ = []} {Δ = Γ₁ ++ DG ∷ []} {Λ = Λ}
          {f = q} {g = gG}
          {h = ⊗L {Γ₀ ++ B ∷ []} {Λ} {DH} {DK} (⊗R gH gK)})))
      eqOuter :
        ⊗L {Γo} {Λ} {DG ⊗ DH} {DK}
          (⊗R
            (⊗L {Γo} {[]} {DG} {DH} (⇐L gG gH))
            gK)
        ≗
        cut Γo t (⊗L {Γo} {Λ} {DG} {DH ⊗ DK} body) refl
      eqOuter =
        ⊗L {Γo} {Λ} {DG ⊗ DH} {DK}
          (~ (⊗L⊗R₁ {Γ = Γo} {Δ = []} {Λ = DK ∷ Λ}
            {A = DG} {B = DH}))
        ∘
        (⊗L {Γo} (⊗L {Γo} (~ ⇐L⊗R₁))
        ∘
        (⊗L {Γo} (⊗L {Γo} eqInner)
        ∘
        (⊗L {Γo} (⊗L {Γo}
          (((~ cutaxA-left Γo (cut (Γo ++ DG ∷ []) q body refl) refl)
            ∘
            ≡to≗ (cut⊗R⊗Lcases++ Γo Λ
              {f = ax} {g = q} {h = body}))))
        ∘
        (⊗L {Γo}
          (~ cut⊗L≗ Γo [] (DK ∷ []) r
            (⊗L {Γo} {Λ} {DG} {DH ⊗ DK} body) refl)
        ∘
           (~ cut⊗L≗ Γo [] [] s
             (⊗L {Γo} {Λ} {DG} {DH ⊗ DK} body) refl)))))
      lhs = ⇐L~⊗' {Γ₀ = Γ₀} {Γ₁ = Γ₁} {Δ₀ = Δ₀} {Δ₁ = Δ₁ ++ Δ₂} {Λ = Λ}
        (intrp DG gG hG)
        (⊗R~' {Γ = Γ₀ ++ B ∷ []} {Δ₀ = Δ₁} {Δ₁ = Δ₂} {Λ = Λ}
          (intrp DH gH hH) (intrp DK gK hK))
      rhs = ⊗R~' {Γ = Γo} {Δ₀ = Δ₀ ++ Δ₁} {Δ₁ = Δ₂} {Λ = Λ}
        (⇐L~⊗' {Γ₀ = Γ₀} {Γ₁ = Γ₁} {Δ₀ = Δ₀} {Δ₁ = Δ₁} {Λ = []}
          (intrp DG gG hG) (intrp DH gH hH))
        (intrp DK gK hK)
      eqh :
        cut [] (MIP.h rhs) t refl ≗ MIP.h lhs
      eqh = ⊗R-assoc-eqh
  in ↜∷ {n = lhs} {n' = rhs} (t , eqOuter , eqh) refl

mip≗⇐L⊗R₁ : ∀ Γ Δ Λ
  {Γ₁ Δ₁ Λ₁ Ω₁ : Cxt} {A B A' B' : Fma}
  {f : Δ₁ ⊢ A} {g : Γ₁ ++ B ∷ Λ₁ ⊢ A'} {h : Ω₁ ⊢ B'}
  → (eq : Γ₁ ++ B ⇐ A ∷ Δ₁ ++ Λ₁ ++ Ω₁ ≡ Γ ++ Δ ++ Λ)
  → MIP≗ Γ Δ Λ (A' ⊗ B')
      (mip Γ Δ Λ (⇐L {Γ₁} {Δ₁} {Λ₁ ++ Ω₁} f (⊗R {Γ₁ ++ B ∷ Λ₁} {Ω₁} g h)) eq)
      (mip Γ Δ Λ (⊗R {Γ₁ ++ B ⇐ A ∷ Δ₁ ++ Λ₁} {Ω₁} (⇐L {Γ₁} {Δ₁} {Λ₁} f g) h) eq)
mip≗⇐L⊗R₁ Γ [] Λ eq = mip[]≗ Γ Λ eq ⇐L⊗R₁
mip≗⇐L⊗R₁ Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {f = f} {g} {h} eq
  with cases++ Γ₁ (Γ ++ E ∷ Δ) (Δ₁ ++ Λ₁ ++ Ω₁) Λ (sym eq)
mip≗⇐L⊗R₁ Γ (E ∷ Δ) .(Ω ++ B ⇐ A ∷ Δ₁ ++ Λ₁ ++ Ω₁)
  {.(Γ ++ E ∷ Δ ++ Ω)} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {f = f} {g} {h} refl
  | inj₂ (Ω , refl , refl)
  rewrite ++?-inj₂ Γ (Δ ++ Ω ++ B ⇐ A ∷ Δ₁ ++ Λ₁) Ω₁ E |
          ++?-inj₂ Γ (Δ ++ Ω ++ B ∷ Λ₁) Ω₁ E |
          ++?-inj₁ (Ω ++ B ⇐ A ∷ Δ₁ ++ Λ₁) Δ Ω₁ |
          ++?-inj₁ (Ω ++ B ∷ Λ₁) Δ Ω₁ |
          cases++-inj₂ Ω (Γ ++ E ∷ Δ) (Δ₁ ++ Λ₁) (B ⇐ A) =
    let G = mip Γ (E ∷ Δ) (Ω ++ B ∷ Λ₁) g refl
    in intrp≗
      (g~ (⇐L⊗R₁
        {Γ = Γ ++ MIP.D G ∷ Ω}
        {Δ = Δ₁}
        {Λ = Λ₁}
        {Ω = Ω₁}
        {A = A}
        {B = B}
        {A' = A'}
        {B' = B'}
        {f = f}
        {g = MIP.g G}
        {h = h}))
... | inj₁ (Ω , eq₁ , eq₂)
  with cases++ Γ₁ Γ Ω (E ∷ Δ) eq₁
... | inj₁ (Ω' , refl , refl)
  with ++? (Ω' ++ E ∷ Δ) Δ₁ Λ (Λ₁ ++ Ω₁) eq₂
... | inj₁ (Ω'' , eq₅ , eq₆)
  with ++? Δ₁ Ω' Ω'' (E ∷ Δ) eq₆
... | inj₁ ([] , refl , refl)
  with ++? Λ₁ (E ∷ Δ) Ω₁ Λ (sym eq₅)
mip≗⇐L⊗R₁ .(Γ₁ ++ B ⇐ A ∷ Ω') (E ∷ Δ) .(Ω'''' ++ Ω₁)
  {Γ₁} {.(Ω')} {.(E ∷ Δ ++ Ω'''')} {Ω₁} {A} {B} {A'} {B'} {f = f} {g} {h} refl
  | inj₁ (.(Ω' ++ E ∷ Δ) , refl , refl)
  | inj₁ (Ω' , refl , refl)
  | inj₁ (.(E ∷ Δ) , refl , refl)
  | inj₁ ([] , refl , refl)
  | inj₁ (Ω'''' , refl , refl)
  rewrite ++?-inj₁ [] Ω' (E ∷ Δ) |
          ++?-inj₂ (Γ₁ ++ B ⇐ A ∷ Ω') (Δ ++ Ω'''') Ω₁ E |
          ++?-inj₂ (Γ₁ ++ B ∷ []) (Δ ++ Ω'''') Ω₁ E |
          ++?-inj₁ Ω'''' Δ Ω₁ |
          cases++-inj₁ Γ₁ (Ω' ++ E ∷ Δ) Ω'''' (B ⇐ A) |
          cases++-inj₁ Γ₁ Ω' (E ∷ Δ) (B ⇐ A) |
          ++?-inj₁ (E ∷ Δ) Ω' Ω'''' |
          ++?-inj₁ [] Ω' (E ∷ Δ) =
    let G = mip (Γ₁ ++ B ∷ []) (E ∷ Δ) Ω'''' g refl
    in intrp≗
      (g~
        (⊗L
          {Γ = Γ₁ ++ B ⇐ A ∷ Ω'}
          {Δ = Ω'''' ++ Ω₁}
          {A = I}
          {B = MIP.D G}
          {C = A' ⊗ B'}
          (⇐L⊗R₁
            {Γ = Γ₁}
            {Δ = Ω' ++ I ∷ []}
            {Λ = MIP.D G ∷ Ω''''}
            {Ω = Ω₁}
            {A = A}
            {B = B}
            {A' = A'}
            {B' = B'}
            {f = IL {Ω'} {[]} f}
            {g = MIP.g G}
            {h = h})
         ∘
         ⊗L⊗R₁
          {Γ = Γ₁ ++ B ⇐ A ∷ Ω'}
          {Δ = Ω''''}
          {Λ = Ω₁}
          {A = I}
          {B = MIP.D G}
          {A' = A'}
          {B' = B'}
          {f = ⇐L {Γ₁} {Ω' ++ I ∷ []} {MIP.D G ∷ Ω''''}
                 (IL {Ω'} {[]} f) (MIP.g G)}
          {g = h}))
... | inj₂ (F , Ω'''' , eq₉ , eq₁₀) with Λ₁
mip≗⇐L⊗R₁ .(Γ₁ ++ B ⇐ A ∷ Ω') (E ∷ Δ) Λ
  {Γ₁} {.(Ω')} {Λ₁} {.(E ∷ Δ ++ Λ)} {A} {B} {A'} {B'} {f = f} {g} {h} refl
  | inj₁ (.(Ω' ++ E ∷ Δ) , refl , refl)
  | inj₁ (Ω' , refl , refl)
  | inj₁ (.(E ∷ Δ) , refl , refl)
  | inj₁ ([] , refl , refl)
  | inj₂ (E , Δ , refl , refl)
  | [] rewrite ++?-inj₁ [] Ω' (E ∷ Δ) |
               ++?-inj₁ [] (Γ₁ ++ B ∷ []) (E ∷ Δ ++ Λ) |
               ++?-inj₁ [] (Γ₁ ++ B ⇐ A ∷ Ω') (E ∷ Δ ++ Λ) =
    intrp≗ (↜∷ (⊗R IR ax , eqg , refl) refl)
  where
    H = mip [] (E ∷ Δ) Λ h refl
    Γo = Γ₁ ++ B ⇐ A ∷ Ω'
    body : Γo ++ I ∷ MIP.D H ∷ Λ ⊢ A' ⊗ B'
    body =
      ⇐L {Γ = Γ₁} {Δ = Ω' ++ I ∷ []} {Λ = MIP.D H ∷ Λ}
        {A = A} {B = B} {C = A' ⊗ B'}
        (IL {Ω'} {[]} f) (⊗R g (MIP.g H))
    irIL : cut Ω' IR (IL {Ω'} {[]} f) refl ≗ f
    irIL rewrite cases++-inj₂ [] Ω' [] I = refl
    eqg : ⊗R (⇐L f g) (MIP.g H) ≗
          cut Γo (⊗R IR ax) (⊗L {Γo} {Λ} {I} {MIP.D H} body) refl
    eqg =
      (~ ⇐L⊗R₁)
      ∘
      (⇐L (~ irIL) refl
      ∘
      ((~ (≡to≗ (cut⇐L-cases++₁ Ω' Γ₁
        {Λ = []} {Λ₁ = MIP.D H ∷ Λ}
        {f = IR} {g = IL {Ω'} {[]} f} {h = ⊗R g (MIP.g H)})))
      ∘
      (cut-cong₂ Γo refl
        (~ cutaxA-left (Γo ++ I ∷ []) body refl)
      ∘
      ≡to≗ (cut⊗R⊗Lcases++ Γo Λ
        {f = IR} {g = ax} {h = body}))))
mip≗⇐L⊗R₁ .(Γ₁ ++ B ⇐ A ∷ Ω') (E ∷ .(Λ₁' ++ F ∷ Ω'''')) Λ
  {Γ₁} {.(Ω')} {Λ₁} {.(F ∷ Ω'''' ++ Λ)}
  {A} {B} {A'} {B'} {f = f} {g} {h} refl
  | inj₁ (.(Ω' ++ E ∷ Λ₁' ++ F ∷ Ω'''') , refl , refl)
  | inj₁ (Ω' , refl , refl)
  | inj₁ (.(E ∷ Λ₁' ++ F ∷ Ω'''') , refl , refl)
  | inj₁ ([] , refl , refl)
  | inj₂ (F , Ω'''' , refl , refl)
  | .E ∷ Λ₁'
  rewrite ++?-inj₁ [] Ω' (E ∷ Λ₁' ++ F ∷ Ω'''') |
          ++?-inj₂ (Γ₁ ++ B ⇐ A ∷ Ω') Λ₁' (F ∷ Ω'''' ++ Λ) E |
          ++?-inj₂ (Γ₁ ++ B ∷ []) Λ₁' (F ∷ Ω'''' ++ Λ) E |
          ++?-inj₂ Λ₁' Ω'''' Λ F |
          cases++-inj₁ Γ₁ (Ω' ++ E ∷ Λ₁') [] (B ⇐ A) |
          cases++-inj₁ Γ₁ Ω' (E ∷ Λ₁') (B ⇐ A) |
          ++?-inj₁ (E ∷ Λ₁') Ω' [] |
          ++?-inj₁ [] Ω' (E ∷ Λ₁') =
  let G = mip (Γ₁ ++ B ∷ []) (E ∷ Λ₁') [] g refl
      H = mip [] (F ∷ Ω'''') Λ h refl
      Γo = Γ₁ ++ B ⇐ A ∷ Ω'
      body : Γo ++ I ∷ MIP.D G ⊗ MIP.D H ∷ Λ ⊢ A' ⊗ B'
      body =
        ⇐L {Γ = Γ₁} {Δ = Ω' ++ I ∷ []} {Λ = MIP.D G ⊗ MIP.D H ∷ Λ}
          {A = A} {B = B} {C = A' ⊗ B'}
          (IL {Ω'} {[]} f)
          (⊗L {Γ₁ ++ B ∷ []} {Λ} {MIP.D G} {MIP.D H}
            (⊗R (MIP.g G) (MIP.g H)))
      q : MIP.D G ∷ MIP.D H ∷ [] ⊢ MIP.D G ⊗ MIP.D H
      q = ⊗R ax ax
      r : I ∷ MIP.D G ∷ MIP.D H ∷ [] ⊢ I ⊗ (MIP.D G ⊗ MIP.D H)
      r = ⊗R ax q
      s : I ⊗ MIP.D G ∷ MIP.D H ∷ [] ⊢ I ⊗ (MIP.D G ⊗ MIP.D H)
      s = ⊗L {[]} r
      t : (I ⊗ MIP.D G) ⊗ MIP.D H ∷ [] ⊢ I ⊗ (MIP.D G ⊗ MIP.D H)
      t = ⊗L {[]} s
      eqInner : ⇐L (IL f) (⊗R (MIP.g G) (MIP.g H)) ≗
                cut (Γo ++ I ∷ []) q body refl
      eqInner =
        (⇐L refl
          ((~ cutaxA-left (Γ₁ ++ B ∷ []) (⊗R (MIP.g G) (MIP.g H)) refl)
           ∘
           (cut-cong₂ (Γ₁ ++ B ∷ []) refl
             (~ cutaxA-left (Γ₁ ++ B ∷ MIP.D G ∷ [])
               (⊗R (MIP.g G) (MIP.g H)) refl)
           ∘
           ≡to≗ (cut⊗R⊗Lcases++ (Γ₁ ++ B ∷ []) Λ
             {f = ax} {g = ax} {h = ⊗R (MIP.g G) (MIP.g H)}))))
        ∘
        (~ (≡to≗ (cut⇐L-cases++-comm₁ Γ₁
          {Γ₁ = []} {Δ = Ω' ++ I ∷ []} {Λ = Λ}
          {f = q} {g = IL {Ω'} {[]} f}
          {h = ⊗L {Γ₁ ++ B ∷ []} {Λ} {MIP.D G} {MIP.D H}
            (⊗R (MIP.g G) (MIP.g H))})))
      eqOuter :
        ⊗L {Γo} {Λ} {I ⊗ MIP.D G} {MIP.D H}
          (⊗R
            (⊗L {Γo} {[]} {I} {MIP.D G}
              (⇐L {Γ = Γ₁} {Δ = Ω' ++ I ∷ []} {Λ = MIP.D G ∷ []}
                {A = A} {B = B} {C = A'}
                (IL {Ω'} {[]} f) (MIP.g G)))
            (MIP.g H))
        ≗
        cut Γo t (⊗L {Γo} {Λ} {I} {MIP.D G ⊗ MIP.D H} body) refl
      eqOuter =
        ⊗L {Γo} {Λ} {I ⊗ MIP.D G} {MIP.D H}
          (~ (⊗L⊗R₁ {Γ = Γo} {Δ = []} {Λ = MIP.D H ∷ Λ}
            {A = I} {B = MIP.D G}))
        ∘
        (⊗L {Γo} (⊗L {Γo} (~ ⇐L⊗R₁))
        ∘
        (⊗L {Γo} (⊗L {Γo} eqInner)
        ∘
        (⊗L {Γo} (⊗L {Γo}
          (((~ cutaxA-left Γo (cut (Γo ++ I ∷ []) q body refl) refl)
            ∘
            ≡to≗ (cut⊗R⊗Lcases++ Γo Λ
              {f = ax} {g = q} {h = body}))))
        ∘
        (⊗L {Γo}
          (~ cut⊗L≗ Γo [] (MIP.D H ∷ []) r
            (⊗L {Γo} {Λ} {I} {MIP.D G ⊗ MIP.D H} body) refl)
        ∘
        (~ cut⊗L≗ Γo [] [] s
          (⊗L {Γo} {Λ} {I} {MIP.D G ⊗ MIP.D H} body) refl)))))
  in intrp≗ (↜∷ (t , eqOuter , refl) refl)
mip≗⇐L⊗R₁ .(Γ₁ ++ B ⇐ A ∷ Ω') (E ∷ .(Ω''' ++ Ω'')) Λ
  {Γ₁} {.(Ω' ++ E ∷ Ω''')} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {f = f} {g} {h} eq
  | inj₁ (.(Ω' ++ E ∷ Ω''' ++ Ω'') , eq₁ , eq₂)
  | inj₁ (Ω' , refl , refl)
  | inj₁ (Ω'' , eq₅ , eq₆)
  | inj₁ (E ∷ Ω''' , refl , refl) with ++? Ω'' Λ₁ Λ Ω₁ eq₅
mip≗⇐L⊗R₁ .(Γ₁ ++ B ⇐ A ∷ Ω') (E ∷ .(Ω''' ++ Λ₁ ++ Ω'''')) Λ
  {Γ₁} {.(Ω' ++ E ∷ Ω''')} {Λ₁} {.(Ω'''' ++ Λ)} {A} {B} {A'} {B'} {f = f} {g} {h} refl
  | inj₁ (.(Ω' ++ E ∷ Ω''' ++ Λ₁ ++ Ω'''') , refl , refl)
  | inj₁ (Ω' , refl , refl)
  | inj₁ (.(Λ₁ ++ Ω'''') , refl , refl)
  | inj₁ (E ∷ Ω''' , refl , refl)
  | inj₁ (Ω'''' , refl , refl)
  rewrite ++?-inj₁ (E ∷ Ω''') Ω' (Λ₁ ++ Ω'''') |
          ++?-inj₂ (Γ₁ ++ B ⇐ A ∷ Ω') (Ω''' ++ Λ₁) (Ω'''' ++ Λ) E
  with Ω''''
... | [] rewrite ++?-inj₁ [] (Ω''' ++ Λ₁) Λ |
                 cases++-inj₁ Γ₁ (Ω' ++ E ∷ Ω''' ++ Λ₁) [] (B ⇐ A) |
               cases++-inj₁ Γ₁ Ω' (E ∷ Ω''' ++ Λ₁) (B ⇐ A) |
               ++?-inj₁ Λ₁ (Ω' ++ E ∷ Ω''') [] |
               ++?-inj₁ (E ∷ Ω''') Ω' Λ₁
  =
    let G = mip Ω' (E ∷ Ω''') [] f refl
        H = mip (Γ₁ ++ B ∷ []) Λ₁ [] g refl
    in intrp≗
      (~-trans
        (⇐L~⊗ refl (mip⊗R₁~ (Γ₁ ++ B ∷ []) Λ₁ Λ))
        (~-trans
          (g~
            (⊗L
              {Γ = Γ₁ ++ B ⇐ A ∷ Ω'}
              {Δ = Λ}
              {A = MIP.D G}
              {B = MIP.D H}
              (⇐L⊗R₁
                {Γ = Γ₁}
                {Δ = Ω' ++ MIP.D G ∷ []}
                {Λ = MIP.D H ∷ []}
                {Ω = Λ}
                {A = A}
                {B = B}
                {A' = A'}
                {B' = B'}
                {f = MIP.g G}
                {g = MIP.g H}
                {h = h})
             ∘
             ⊗L⊗R₁
              {Γ = Γ₁ ++ B ⇐ A ∷ Ω'}
              {Δ = []}
              {Λ = Λ}
              {A = MIP.D G}
              {B = MIP.D H}
              {A' = A'}
              {B' = B'}
              {f = ⇐L {Γ₁} {Ω' ++ MIP.D G ∷ []} {MIP.D H ∷ []}
                     (MIP.g G) (MIP.g H)}
              {g = h}))
          refl))
... | F ∷ Ω''''' rewrite ++?-inj₂ (Ω''' ++ Λ₁) Ω''''' Λ F =
  let G = mip Ω' (E ∷ Ω''') [] f refl
      H = mip (Γ₁ ++ B ∷ []) Λ₁ [] g refl
      K = mip [] (F ∷ Ω''''') Λ h refl
  in intrp≗
    (~-trans
      (⇐L~⊗ refl (mip⊗Rmid~ (Γ₁ ++ B ∷ []) Λ₁ F Ω''''' Λ))
      (~-trans
        (⇐L⊗R₁-assoc~ G H K)
        (⊗R~ (~-sym (mip⇐L~⊗mid-base Γ₁ Ω' (E ∷ Ω''') Λ₁ [])) refl)))
mip≗⇐L⊗R₁ .(Γ₁ ++ B ⇐ A ∷ Ω') (E ∷ .(Ω''' ++ Ω'')) .(F ∷ Ω'''' ++ Ω₁)
  {Γ₁} {.(Ω' ++ E ∷ Ω''')} {.(Ω'' ++ F ∷ Ω'''')} {Ω₁} {A} {B} {A'} {B'} {f = f} {g} {h} refl
  | inj₁ (.(Ω' ++ E ∷ Ω''' ++ Ω'') , refl , refl)
  | inj₁ (Ω' , refl , refl)
  | inj₁ (Ω'' , refl , refl)
  | inj₁ (E ∷ Ω''' , refl , refl)
  | inj₂ (F , Ω'''' , refl , refl)
  rewrite ++?-inj₁ (E ∷ Ω''') Ω' Ω'' |
          ++?-inj₂ (Γ₁ ++ B ⇐ A ∷ Ω') (Ω''' ++ Ω'' ++ F ∷ Ω'''') Ω₁ E |
          ++?-inj₁ (F ∷ Ω'''') (Ω''' ++ Ω'') Ω₁ =
    let G = mip Ω' (E ∷ Ω''') [] f refl
        H = mip (Γ₁ ++ B ∷ []) Ω'' (F ∷ Ω'''') g refl
    in intrp≗
      (~-trans
        (⇐L~⊗ refl (mip⊗R₁Λ~ (Γ₁ ++ B ∷ []) Ω'' (F ∷ Ω'''') Ω₁))
        (~-trans
          (g~
            (⊗L
              {Γ = Γ₁ ++ B ⇐ A ∷ Ω'}
              {Δ = F ∷ Ω'''' ++ Ω₁}
              {A = MIP.D G}
              {B = MIP.D H}
              (⇐L⊗R₁
                {Γ = Γ₁}
                {Δ = Ω' ++ MIP.D G ∷ []}
                {Λ = MIP.D H ∷ F ∷ Ω''''}
                {Ω = Ω₁}
                {A = A}
                {B = B}
                {A' = A'}
                {B' = B'}
                {f = MIP.g G}
                {g = MIP.g H}
                {h = h})
             ∘
             ⊗L⊗R₁
              {Γ = Γ₁ ++ B ⇐ A ∷ Ω'}
              {Δ = F ∷ Ω''''}
              {Λ = Ω₁}
              {A = MIP.D G}
              {B = MIP.D H}
              {A' = A'}
              {B' = B'}
              {f = ⇐L {Γ₁} {Ω' ++ MIP.D G ∷ []} {MIP.D H ∷ F ∷ Ω''''}
                     (MIP.g G) (MIP.g H)}
              {g = h}))
          (⊗R~₁ (~-sym (mip⇐L~⊗mid-base Γ₁ Ω' (E ∷ Ω''') Ω'' (F ∷ Ω''''))) refl)))
mip≗⇐L⊗R₁ .(Γ₁ ++ B ⇐ A ∷ Δ₁ ++ F ∷ Ω''') (E ∷ Δ) Λ
  {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {f = f} {g} {h} eq
  | inj₁ (.(Δ₁ ++ F ∷ Ω''' ++ E ∷ Δ) , refl , eq₂)
  | inj₁ (.(Δ₁ ++ F ∷ Ω''') , refl , refl)
  | inj₁ (.(F ∷ Ω''' ++ E ∷ Δ) , eq₅ , refl)
  | inj₂ (F , Ω''' , refl , refl)
  with ++? (F ∷ Ω''') Λ₁ (E ∷ Δ ++ Λ) Ω₁ eq₅
mip≗⇐L⊗R₁ .(Γ₁ ++ B ⇐ A ∷ Δ₁ ++ F ∷ Ω''') (E ∷ Δ) Λ
  {Γ₁} {Δ₁} {[]} {Ω₁} {A} {B} {A'} {B'} {f = f} {g} {h} refl
  | inj₁ (.(Δ₁ ++ F ∷ Ω''' ++ E ∷ Δ) , refl , refl)
  | inj₁ (.(Δ₁ ++ F ∷ Ω''') , refl , refl)
  | inj₁ (.(F ∷ Ω''' ++ E ∷ Δ) , refl , refl)
  | inj₂ (F , Ω''' , refl , refl)
  | inj₁ (.(F ∷ Ω''') , refl , refl)
  rewrite ++?-inj₂ Δ₁ Ω''' (E ∷ Δ) F |
          ++?-inj₁ (F ∷ Ω''') (Γ₁ ++ B ∷ []) (E ∷ Δ ++ Λ) |
          ++?-inj₁ (F ∷ Ω''') (Γ₁ ++ B ⇐ A ∷ Δ₁) (E ∷ Δ ++ Λ) =
    intrp≗ (g~ ⇐L⊗R₁)
mip≗⇐L⊗R₁ .(Γ₁ ++ B ⇐ A ∷ Δ₁ ++ F ∷ Ω''') (E ∷ Δ) Λ
  {Γ₁} {Δ₁} {F ∷ Λ₁'} {Ω₁} {A} {B} {A'} {B'} {f = f} {g} {h} refl
  | inj₁ (.(Δ₁ ++ F ∷ Ω''' ++ E ∷ Δ) , refl , refl)
  | inj₁ (.(Δ₁ ++ F ∷ Ω''') , refl , refl)
  | inj₁ (.(F ∷ Ω''' ++ E ∷ Δ) , refl , refl)
  | inj₂ (.F , Ω''' , refl , refl)
  | inj₁ (Ω'''' , refl , refl)
  rewrite ++?-inj₂ Δ₁ (Λ₁' ++ Ω'''') (E ∷ Δ) F |
          ++?-inj₁ Ω'''' (Γ₁ ++ B ∷ F ∷ Λ₁') (E ∷ Δ ++ Λ) |
          ++?-inj₁ Ω'''' (Γ₁ ++ B ⇐ A ∷ Δ₁ ++ F ∷ Λ₁') (E ∷ Δ ++ Λ) =
    intrp≗ (g~ ⇐L⊗R₁)
mip≗⇐L⊗R₁ .(Γ₁ ++ B ⇐ A ∷ Δ₁ ++ F ∷ Ω''') (E ∷ Δ) Λ
  {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {f = f} {g} {h} eq
  | inj₁ (.(Δ₁ ++ F ∷ Ω''' ++ E ∷ Δ) , refl , eq₂)
  | inj₁ (.(Δ₁ ++ F ∷ Ω''') , refl , refl)
  | inj₁ (.(F ∷ Ω''' ++ E ∷ Δ) , eq₅ , refl)
  | inj₂ (F , Ω''' , refl , refl)
  | inj₂ (G , Ω'''' , eq₉ , eq₁₀) with inj∷ eq₁₀
... | refl , eq₁₀' with ++? Ω'''' Δ Ω₁ Λ eq₁₀'
mip≗⇐L⊗R₁ .(Γ₁ ++ B ⇐ A ∷ Δ₁ ++ F ∷ Ω''') (E ∷ Δ) .(Ω''''' ++ Ω₁)
  {Γ₁} {Δ₁} {.(F ∷ Ω''' ++ E ∷ Δ ++ Ω''''')} {Ω₁} {A} {B} {A'} {B'} {f = f} {g} {h} refl
  | inj₁ (.(Δ₁ ++ F ∷ Ω''' ++ E ∷ Δ) , refl , refl)
  | inj₁ (.(Δ₁ ++ F ∷ Ω''') , refl , refl)
  | inj₁ (.(F ∷ Ω''' ++ E ∷ Δ) , refl , refl)
  | inj₂ (F , Ω''' , refl , refl)
  | inj₂ (.E , .(Δ ++ Ω''''') , refl , refl)
  | refl , refl
  | inj₁ (Ω''''' , refl , refl)
  rewrite ++?-inj₂ Δ₁ Ω''' (E ∷ Δ) F |
          ++?-inj₂ (Γ₁ ++ B ⇐ A ∷ Δ₁ ++ F ∷ Ω''') (Δ ++ Ω''''') Ω₁ E |
          ++?-inj₂ (Γ₁ ++ B ∷ F ∷ Ω''') (Δ ++ Ω''''') Ω₁ E |
          ++?-inj₁ Ω''''' Δ Ω₁ |
          cases++-inj₁ Γ₁ (Δ₁ ++ F ∷ Ω''' ++ E ∷ Δ) Ω''''' (B ⇐ A) |
          cases++-inj₁ Γ₁ (Δ₁ ++ F ∷ Ω''') (E ∷ Δ) (B ⇐ A) |
          ++?-inj₁ (F ∷ Ω''' ++ E ∷ Δ) Δ₁ Ω''''' |
          ++?-inj₂ Δ₁ Ω''' (E ∷ Δ) F =
    intrp≗ (g~ ⇐L⊗R₁)
mip≗⇐L⊗R₁ .(Γ₁ ++ B ⇐ A ∷ Δ₁ ++ F ∷ Ω''') (E ∷ .(Ω'''' ++ H ∷ Ω''''')) Λ
  {Γ₁} {Δ₁} {.(F ∷ Ω''' ++ E ∷ Ω'''')} {.(H ∷ Ω''''' ++ Λ)}
  {A} {B} {A'} {B'} {f = f} {g} {h} refl
  | inj₁ (.(Δ₁ ++ F ∷ Ω''' ++ E ∷ Ω'''' ++ H ∷ Ω''''') , refl , refl)
  | inj₁ (.(Δ₁ ++ F ∷ Ω''') , refl , refl)
  | inj₁ (.(F ∷ Ω''' ++ E ∷ Ω'''' ++ H ∷ Ω''''') , refl , refl)
  | inj₂ (F , Ω''' , refl , refl)
  | inj₂ (.E , Ω'''' , refl , refl)
  | refl , refl
  | inj₂ (H , Ω''''' , refl , refl)
  rewrite ++?-inj₂ Δ₁ Ω''' (E ∷ Ω'''' ++ H ∷ Ω''''') F |
          ++?-inj₂ (Γ₁ ++ B ∷ F ∷ Ω''') Ω'''' (H ∷ Ω''''' ++ Λ) E |
          ++?-inj₂ Ω'''' Ω''''' Λ H |
          ++?-inj₂ (Γ₁ ++ B ⇐ A ∷ Δ₁ ++ F ∷ Ω''') Ω'''' (H ∷ Ω''''' ++ Λ) E |
          ++?-inj₂ Ω'''' Ω''''' Λ H |
          cases++-inj₁ Γ₁ (Δ₁ ++ F ∷ Ω''' ++ E ∷ Ω'''') [] (B ⇐ A) |
          cases++-inj₁ Γ₁ (Δ₁ ++ F ∷ Ω''') (E ∷ Ω'''') (B ⇐ A) |
          ++?-inj₁ (F ∷ Ω''' ++ E ∷ Ω'''') Δ₁ [] |
          ++?-inj₂ Δ₁ Ω''' (E ∷ Ω'''') F =
    intrp≗
      (g~ ((~ ⊗L⇐L-comm₂) ∘
        ⊗L {Γ₁ ++ B ⇐ A ∷ Δ₁ ++ F ∷ Ω'''} ⇐L⊗R₁))
mip≗⇐L⊗R₁ .(Γ₁ ++ B ⇐ A ∷ Ω') (E ∷ Δ) .(F ∷ Ω'' ++ Λ₁ ++ Ω₁)
  {Γ₁} {.(Ω' ++ E ∷ Δ ++ F ∷ Ω'')} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {f = f} {g} {h} refl
  | inj₁ (.(Ω' ++ E ∷ Δ) , refl , refl) | inj₁ (Ω' , refl , refl)
  | inj₂ (F , Ω'' , refl , refl)
  rewrite ++?-inj₂ (Γ₁ ++ B ⇐ A ∷ Ω') (Δ ++ F ∷ Ω'' ++ Λ₁) Ω₁ E |
          ++?-inj₁ (F ∷ Ω'' ++ Λ₁) Δ Ω₁ |
          cases++-inj₁ Γ₁ (Ω' ++ E ∷ Δ) (F ∷ Ω'' ++ Λ₁) (B ⇐ A) |
          cases++-inj₁ Γ₁ Ω' (E ∷ Δ) (B ⇐ A) |
          ++?-inj₂ (Ω' ++ E ∷ Δ) Ω'' Λ₁ F =
    intrp≗ (g~ ⇐L⊗R₁)
mip≗⇐L⊗R₁ Γ (E ∷ Δ) Λ {Γ₁} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {f = f} {g} {h} eq
  | inj₁ (Ω , eq₁ , eq₂) | inj₂ (Ω' , eq₃ , eq₄)
  with cases∷ Ω' eq₃
mip≗⇐L⊗R₁ Γ (.(B ⇐ A) ∷ Ω) Λ
  {.(Γ)} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {f = f} {g} {h} eq
  | inj₁ (Ω , refl , eq₂) | inj₂ ([] , refl , refl)
  | inj₁ (refl , refl , refl)
  with ++? Ω Δ₁ Λ (Λ₁ ++ Ω₁) eq₂
... | inj₁ (Ω'' , eq₅ , refl)
  with ++? Λ₁ Ω'' Ω₁ Λ (sym eq₅)
mip≗⇐L⊗R₁ Γ (.(B ⇐ A) ∷ .(Δ₁ ++ Ω'')) .(Ω''' ++ Ω₁)
  {.(Γ)} {Δ₁} {.(Ω'' ++ Ω''')} {Ω₁} {A} {B} {A'} {B'} {f = f} {g} {h} refl
  | inj₁ (.(Δ₁ ++ Ω'') , refl , refl) | inj₂ ([] , refl , refl)
  | inj₁ (refl , refl , refl)
  | inj₁ (Ω'' , refl , refl)
  | inj₁ (Ω''' , refl , refl)
  rewrite ++?-inj₂ Γ (Ω'' ++ Ω''') Ω₁ B |
          ++?-inj₁ Ω''' Ω'' Ω₁ |
          ++?-inj₂ Γ (Δ₁ ++ Ω'' ++ Ω''') Ω₁ (B ⇐ A) |
          ++?-inj₁ Ω''' (Δ₁ ++ Ω'') Ω₁ |
          cases++-inj₁ Γ (Δ₁ ++ Ω'') Ω''' (B ⇐ A) |
          cases++-inj₂ [] Γ (Δ₁ ++ Ω'') (B ⇐ A) |
          ++?-inj₁ Ω'' Δ₁ Ω''' =
    intrp≗ refl
mip≗⇐L⊗R₁ Γ (.(B ⇐ A) ∷ .(Δ₁ ++ Λ₁ ++ F ∷ Ω''')) Λ
  {.(Γ)} {Δ₁} {Λ₁} {.(F ∷ Ω''' ++ Λ)} {A} {B} {A'} {B'} {f = f} {g} {h} refl
  | inj₁ (.(Δ₁ ++ Λ₁ ++ F ∷ Ω''') , refl , refl) | inj₂ ([] , refl , refl)
  | inj₁ (refl , refl , refl)
  | inj₁ (.(Λ₁ ++ F ∷ Ω''') , refl , refl)
  | inj₂ (F , Ω''' , refl , refl)
  rewrite ++?-inj₂ Γ Λ₁ (F ∷ Ω''' ++ Λ) B |
          ++?-inj₂ Λ₁ Ω''' Λ F |
          ++?-inj₂ Γ (Δ₁ ++ Λ₁) (F ∷ Ω''' ++ Λ) (B ⇐ A) |
          ++?-inj₂ (Δ₁ ++ Λ₁) Ω''' Λ F |
          cases++-inj₁ Γ (Δ₁ ++ Λ₁) [] (B ⇐ A) |
          cases++-inj₂ [] Γ (Δ₁ ++ Λ₁) (B ⇐ A) |
          ++?-inj₁ Λ₁ Δ₁ [] =
    intrp≗ (h~ ⇐L⊗R₁)
mip≗⇐L⊗R₁ Γ (.(B ⇐ A) ∷ Ω) .(F ∷ Ω'' ++ Λ₁ ++ Ω₁)
  {.(Γ)} {.(Ω ++ F ∷ Ω'')} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {f = f} {g} {h} refl
  | inj₁ (Ω , refl , refl) | inj₂ ([] , refl , refl)
  | inj₁ (refl , refl , refl)
  | inj₂ (F , Ω'' , refl , refl)
  rewrite ++?-inj₂ Γ Λ₁ Ω₁ B |
          ++?-inj₂ Γ (Ω ++ F ∷ Ω'' ++ Λ₁) Ω₁ (B ⇐ A) |
          ++?-inj₁ (F ∷ Ω'' ++ Λ₁) Ω Ω₁ |
          cases++-inj₁ Γ Ω (F ∷ Ω'' ++ Λ₁) (B ⇐ A) |
          cases++-inj₂ [] Γ Ω (B ⇐ A) |
          ++?-inj₂ Ω Ω'' Λ₁ F =
    intrp≗ (g~ ⇐L⊗R₁)
mip≗⇐L⊗R₁ Γ (E ∷ .(Ω'' ++ B ⇐ A ∷ Ω)) Λ
  {.(Γ ++ E ∷ Ω'')} {Δ₁} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {f = f} {g} {h} eq
  | inj₁ (Ω , refl , eq₂) | inj₂ (.(E ∷ Ω'') , refl , refl)
  | inj₂ (Ω'' , refl , refl)
  with ++? Ω Δ₁ Λ (Λ₁ ++ Ω₁) eq₂
... | inj₁ (Ω''' , eq₅ , refl)
  with ++? Λ₁ Ω''' Ω₁ Λ (sym eq₅)
mip≗⇐L⊗R₁ Γ (E ∷ .(Ω'' ++ B ⇐ A ∷ Δ₁ ++ Ω''')) .(Ω'''' ++ Ω₁)
  {.(Γ ++ E ∷ Ω'')} {Δ₁} {.(Ω''' ++ Ω'''')} {Ω₁} {A} {B} {A'} {B'} {f = f} {g} {h} refl
  | inj₁ (.(Δ₁ ++ Ω''') , refl , refl) | inj₂ (.(E ∷ Ω'') , refl , refl)
  | inj₂ (Ω'' , refl , refl)
  | inj₁ (Ω''' , refl , refl)
  | inj₁ (Ω'''' , refl , refl)
  rewrite ++?-inj₂ Γ (Ω'' ++ B ∷ Ω''' ++ Ω'''') Ω₁ E |
          ++?-inj₁ Ω'''' (Ω'' ++ B ∷ Ω''') Ω₁ |
          ++?-inj₂ Γ (Ω'' ++ B ⇐ A ∷ Δ₁ ++ Ω''' ++ Ω'''') Ω₁ E |
          ++?-inj₁ Ω'''' (Ω'' ++ B ⇐ A ∷ Δ₁ ++ Ω''') Ω₁ |
          cases++-inj₁ (Γ ++ E ∷ Ω'') (Δ₁ ++ Ω''') Ω'''' (B ⇐ A) |
          cases++-inj₂ (E ∷ Ω'') Γ (Δ₁ ++ Ω''') (B ⇐ A) |
          ++?-inj₁ Ω''' Δ₁ Ω'''' =
    intrp≗ refl
mip≗⇐L⊗R₁ Γ (E ∷ .(Ω'' ++ B ⇐ A ∷ Δ₁ ++ Λ₁ ++ F ∷ Ω'''')) Λ
  {.(Γ ++ E ∷ Ω'')} {Δ₁} {Λ₁} {.(F ∷ Ω'''' ++ Λ)} {A} {B} {A'} {B'} {f = f} {g} {h} refl
  | inj₁ (.(Δ₁ ++ Λ₁ ++ F ∷ Ω'''') , refl , refl) | inj₂ (.(E ∷ Ω'') , refl , refl)
  | inj₂ (Ω'' , refl , refl)
  | inj₁ (.(Λ₁ ++ F ∷ Ω'''') , refl , refl)
  | inj₂ (F , Ω'''' , refl , refl)
  rewrite ++?-inj₂ Γ (Ω'' ++ B ∷ Λ₁) (F ∷ Ω'''' ++ Λ) E |
          ++?-inj₂ (Ω'' ++ B ∷ Λ₁) Ω'''' Λ F |
          ++?-inj₂ Γ (Ω'' ++ B ⇐ A ∷ Δ₁ ++ Λ₁) (F ∷ Ω'''' ++ Λ) E |
          ++?-inj₂ (Ω'' ++ B ⇐ A ∷ Δ₁ ++ Λ₁) Ω'''' Λ F |
          cases++-inj₁ (Γ ++ E ∷ Ω'') (Δ₁ ++ Λ₁) [] (B ⇐ A) |
          cases++-inj₂ (E ∷ Ω'') Γ (Δ₁ ++ Λ₁) (B ⇐ A) |
          ++?-inj₁ Λ₁ Δ₁ [] =
    intrp≗ (h~ ⇐L⊗R₁)
mip≗⇐L⊗R₁ Γ (E ∷ .(Ω'' ++ B ⇐ A ∷ Ω)) .(F ∷ Ω''' ++ Λ₁ ++ Ω₁)
  {.(Γ ++ E ∷ Ω'')} {.(Ω ++ F ∷ Ω''')} {Λ₁} {Ω₁} {A} {B} {A'} {B'} {f = f} {g} {h} refl
  | inj₁ (Ω , refl , refl) | inj₂ (.(E ∷ Ω'') , refl , refl)
  | inj₂ (Ω'' , refl , refl)
  | inj₂ (F , Ω''' , refl , refl)
  rewrite ++?-inj₂ Γ (Ω'' ++ B ∷ Λ₁) Ω₁ E |
          ++?-inj₁ Λ₁ (Ω'' ++ B ∷ []) Ω₁ |
          ++?-inj₂ Γ (Ω'' ++ B ⇐ A ∷ Ω ++ F ∷ Ω''' ++ Λ₁) Ω₁ E |
          ++?-inj₁ (F ∷ Ω''' ++ Λ₁) (Ω'' ++ B ⇐ A ∷ Ω) Ω₁ |
          cases++-inj₁ (Γ ++ E ∷ Ω'') Ω (F ∷ Ω''' ++ Λ₁) (B ⇐ A) |
          cases++-inj₂ (E ∷ Ω'') Γ Ω (B ⇐ A) |
          ++?-inj₂ Ω Ω''' Λ₁ F =
    intrp≗ (g~ ⇐L⊗R₁)
