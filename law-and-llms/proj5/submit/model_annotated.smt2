; ===========================================================
; File: model_annotated.smt2
; Base SMT Model for 26 USC 152(a)-(d) with Annotations
; ===========================================================

(set-logic ALL)
(set-option :unsat_core true) ; Enable unsat core generation

; --- Declare Sorts and Constants ---
(declare-sort Person)
(declare-const TP Person) ; Generic Taxpayer placeholder
(declare-const PD Person) ; Generic Potential Dependent placeholder

; --- Declare Functions (Properties, Relationships, Thresholds) ---
; Basic Properties
(declare-fun Age (Person) Int)
(declare-fun GrossIncome (Person) Int)
(declare-fun IsStudent (Person) Bool)
(declare-fun IsPermanentlyTotallyDisabled (Person) Bool)
(declare-fun IsCitizenOrNationalOrResident (Person) Bool) ; US/Nat/Resid(US/Can/Mex)
(declare-fun IsUSCitizenOrNational (Person) Bool)

; Relationships (PD relative to TP)
(declare-fun IsChildOrDescendant (Person Person) Bool)
(declare-fun IsSiblingOrStepSibling (Person Person) Bool)
(declare-fun IsDescendantOfSiblingEtc (Person Person) Bool)
(declare-fun IsParentOrAncestor (Person Person) Bool)
(declare-fun IsStepParent (Person Person) Bool)
(declare-fun IsSiblingOfParent (Person Person) Bool) ; Aunt/Uncle
(declare-fun IsChildOfSibling (Person Person) Bool)   ; Niece/Nephew
(declare-fun IsInLaw (Person Person) Bool)
(declare-fun IsHouseholdMember (Person Person) Bool) ; Lives w/ TP & member of household

; Residency
(declare-fun ResidesWithTPMoreThanHalfYear (Person Person) Bool)
(declare-fun HasSamePrincipalPlaceOfAbode (Person Person) Bool)

; Support
(declare-fun PDProvidesOverHalfOwnSupport (Person) Bool)
(declare-fun TPProvidesOverHalfSupport (Person Person) Bool)
(declare-fun HasMultipleSupportAgreement (Person Person) Bool) ; Simplified

; Filing Status / Other Rules
(declare-fun FilesJointReturn (Person) Bool)
(declare-fun FilesJointReturnOnlyForRefund (Person) Bool)
(declare-fun IsDependentOfAnyTaxpayer (Person) Bool) ; Simplified b(1) check
(declare-fun IsQC_OfAnyOtherTaxpayer (Person) Bool) ; Simplified d(1)(D) check

; Thresholds
(declare-const ExemptionAmountThreshold Int) ; Gross income limit for QR

; Exception Helpers
(declare-fun IsAdoptedChildLivingWithUSCitizenTPHouseholdMember (Person Person) Bool) ; For b(3)(B)

; --- Define Helper Predicates (Annotated) ---

; QC Relationship Test (c)(2)
(define-fun QC_Relationship ((tp Person) (pd Person)) Bool
  (or (IsChildOrDescendant pd tp)
      (IsSiblingOrStepSibling pd tp)
      (IsDescendantOfSiblingEtc pd tp)))
(assert (! (forall ((tp Person) (pd Person))
            (= (QC_Relationship tp pd)
               (or (IsChildOrDescendant pd tp)
                   (IsSiblingOrStepSibling pd tp)
                   (IsDescendantOfSiblingEtc pd tp))))
         :named rule_qc_relationship))

; QC Age Test (c)(3)
(define-fun QC_AgeRequirement ((tp Person) (pd Person)) Bool
  (and (< (Age pd) (Age tp))
       (or (IsPermanentlyTotallyDisabled pd)
           (< (Age pd) 19)
           (and (IsStudent pd) (< (Age pd) 24)))))
(assert (! (forall ((tp Person) (pd Person))
            (= (QC_AgeRequirement tp pd)
               (and (< (Age pd) (Age tp)) ; Must be younger
                    (or (IsPermanentlyTotallyDisabled pd) ; Disabled OR
                        (< (Age pd) 19)                 ; Under 19 OR
                        (and (IsStudent pd) (< (Age pd) 24)))))) ; Student under 24
         :named rule_qc_age))

; QC Residency Test (c)(1)(B) - Simplified as direct predicate
(assert (! (forall ((tp Person) (pd Person))
            (= (ResidesWithTPMoreThanHalfYear tp pd) (ResidesWithTPMoreThanHalfYear tp pd))) ; Placeholder identity
         :named rule_qc_residency)) ; Name associated with the function itself

; QC Support Test (c)(1)(D) - Simplified as direct predicate
(assert (! (forall ((pd Person))
            (= (not (PDProvidesOverHalfOwnSupport pd)) (not (PDProvidesOverHalfOwnSupport pd))))
         :named rule_qc_support))

; QC Joint Return Test (c)(1)(E)
(define-fun QC_JointReturnTestFails ((pd Person)) Bool
    (and (FilesJointReturn pd) (not (FilesJointReturnOnlyForRefund pd))))
(assert (! (forall ((pd Person))
            (= (QC_JointReturnTestFails pd)
               (and (FilesJointReturn pd) (not (FilesJointReturnOnlyForRefund pd)))))
         :named rule_qc_joint_return))

; QR Relationship Test (d)(2)
(define-fun QR_Relationship ((tp Person) (pd Person)) Bool
  (or (IsChildOrDescendant pd tp)
      (IsSiblingOrStepSibling pd tp)
      (IsParentOrAncestor pd tp)
      (IsStepParent pd tp)
      (IsChildOfSibling pd tp)
      (IsSiblingOfParent pd tp)
      (IsInLaw pd tp)
      (and (HasSamePrincipalPlaceOfAbode pd tp) (IsHouseholdMember pd tp))))
(assert (! (forall ((tp Person) (pd Person))
            (= (QR_Relationship tp pd)
               (or (IsChildOrDescendant pd tp)
                   (IsSiblingOrStepSibling pd tp)
                   (IsParentOrAncestor pd tp)
                   (IsStepParent pd tp)
                   (IsChildOfSibling pd tp) ; niece/nephew
                   (IsSiblingOfParent pd tp) ; aunt/uncle
                   (IsInLaw pd tp)
                   ; Non-relative household member test (d)(2)(H)
                   (and (HasSamePrincipalPlaceOfAbode pd tp) (IsHouseholdMember pd tp)))))
         :named rule_qr_relationship))
; Specific annotation for household member part of QR relationship
(assert (! (forall ((tp Person) (pd Person))
            (=> (and (HasSamePrincipalPlaceOfAbode pd tp) (IsHouseholdMember pd tp))
                (QR_Relationship tp pd)))
        :named rule_qr_relationship_household))
; Specific annotation for parent part of QR relationship
(assert (! (forall ((tp Person) (pd Person))
            (=> (IsParentOrAncestor pd tp) (QR_Relationship tp pd)))
        :named rule_qr_relationship_parent))


; QR Income Test (d)(1)(B)
(define-fun QR_IncomeTest ((pd Person)) Bool
    (< (GrossIncome pd) ExemptionAmountThreshold))
(assert (! (forall ((pd Person))
            (= (QR_IncomeTest pd) (< (GrossIncome pd) ExemptionAmountThreshold)))
        :named rule_qr_income))

; QR Support Test (d)(1)(C) & (d)(3) - Simplified
(define-fun QR_SupportRequirement ((tp Person) (pd Person)) Bool
  (or (TPProvidesOverHalfSupport tp pd)
      (HasMultipleSupportAgreement tp pd)))
(assert (! (forall ((tp Person) (pd Person))
            (= (QR_SupportRequirement tp pd)
               (or (TPProvidesOverHalfSupport tp pd)
                   (HasMultipleSupportAgreement tp pd))))
         :named rule_qr_support))

; QR Not QC Test (d)(1)(D) - Self
(assert (! (forall ((tp Person) (pd Person))
            (=> (IsQualifyingChild tp pd) (not (IsQualifyingRelative tp pd)))) ; Part of QR def below
         :named rule_qr_not_qc_self))

; QR Not QC Test (d)(1)(D) - Other Taxpayer (Simplified predicate)
(assert (! (forall ((pd Person))
            (=> (IsQC_OfAnyOtherTaxpayer pd) false)) ; Placeholder logic for annotation
         :named rule_qr_not_qc_other))


; Exception: Dependent has Dependent (b)(1) - Simplified
(assert (! (forall ((pd Person)) (=> (IsDependentOfAnyTaxpayer pd) true)) ; Placeholder
         :named rule_ex_b1_dep_has_dep))

; Exception: Married Filing Jointly (b)(2)
(assert (! (forall ((pd Person)) (=> (FilesJointReturn pd) true)) ; Placeholder
         :named rule_ex_b2_mfs)) ; Note: QC rule handles the 'only for refund' part

; Exception: Citizenship/Residency (b)(3)
(define-fun Exception_Citizenship ((tp Person) (pd Person)) Bool
  (not (or (IsCitizenOrNationalOrResident pd)
           (IsAdoptedChildLivingWithUSCitizenTPHouseholdMember tp pd))))
(assert (! (forall ((tp Person) (pd Person))
            (= (Exception_Citizenship tp pd)
               (not (or (IsCitizenOrNationalOrResident pd)
                        (IsAdoptedChildLivingWithUSCitizenTPHouseholdMember tp pd)))))
         :named rule_ex_b3_citizen))

; Combined Exceptions (b)
(define-fun ExceptionApplies ((tp Person) (pd Person)) Bool
  (or (IsDependentOfAnyTaxpayer pd) ; b(1) Simplified
      (FilesJointReturn pd)         ; b(2) Simplified (ignores QC refund exception here)
      (Exception_Citizenship tp pd) ; b(3)
  ))
(assert (! (forall ((tp Person) (pd Person))
            (= (ExceptionApplies tp pd)
               (or (IsDependentOfAnyTaxpayer pd)
                   (FilesJointReturn pd) ; Simplified check here
                   (Exception_Citizenship tp pd))))
         :named def_exception_applies))


; --- Define Qualifying Child (QC) --- (c)
(define-fun IsQualifyingChild ((tp Person) (pd Person)) Bool
  (and (QC_Relationship tp pd)                ; (c)(1)(A) - rule_qc_relationship
       (ResidesWithTPMoreThanHalfYear tp pd)  ; (c)(1)(B) - rule_qc_residency
       (QC_AgeRequirement tp pd)              ; (c)(1)(C) - rule_qc_age
       (not (PDProvidesOverHalfOwnSupport pd)); (c)(1)(D) - rule_qc_support
       (not (QC_JointReturnTestFails pd))     ; (c)(1)(E) - rule_qc_joint_return
       ; Ignoring tie-breaker rules (c)(4) for simplicity
))
(assert (! (forall ((tp Person) (pd Person))
            (= (IsQualifyingChild tp pd)
               (and (QC_Relationship tp pd)
                    (ResidesWithTPMoreThanHalfYear tp pd)
                    (QC_AgeRequirement tp pd)
                    (not (PDProvidesOverHalfOwnSupport pd))
                    (not (QC_JointReturnTestFails pd)))))
         :named def_is_qualifying_child))


; --- Define Qualifying Relative (QR) --- (d)
(define-fun IsQualifyingRelative ((tp Person) (pd Person)) Bool
  (and (QR_Relationship tp pd)             ; (d)(1)(A) - rule_qr_relationship
       (QR_IncomeTest pd)                  ; (d)(1)(B) - rule_qr_income
       (QR_SupportRequirement tp pd)       ; (d)(1)(C) - rule_qr_support
       (not (IsQualifyingChild tp pd))     ; (d)(1)(D) - rule_qr_not_qc_self
       (not (IsQC_OfAnyOtherTaxpayer pd))  ; (d)(1)(D) - rule_qr_not_qc_other (simplified)
))
(assert (! (forall ((tp Person) (pd Person))
            (= (IsQualifyingRelative tp pd)
               (and (QR_Relationship tp pd)
                    (QR_IncomeTest pd)
                    (QR_SupportRequirement tp pd)
                    (not (IsQualifyingChild tp pd))
                    (not (IsQC_OfAnyOtherTaxpayer pd)))))
        :named def_is_qualifying_relative))

; --- Define Dependent (Overall) --- (a)
(define-fun IsDependent ((tp Person) (pd Person)) Bool
  (and (not (ExceptionApplies tp pd)) ; No exceptions apply (b) - def_exception_applies
       (or (IsQualifyingChild tp pd)  ; Is QC (c)           - def_is_qualifying_child
           (IsQualifyingRelative tp pd) ; Is QR (d)           - def_is_qualifying_relative
       )))
(assert (! (forall ((tp Person) (pd Person))
            (= (IsDependent tp pd)
               (and (not (ExceptionApplies tp pd))
                    (or (IsQualifyingChild tp pd)
                        (IsQualifyingRelative tp pd)))))
        :named def_is_dependent))

; Placeholder for exemption amount - set in scenario files
(assert (! (> ExemptionAmountThreshold 0) :named fact_threshold_positive))
