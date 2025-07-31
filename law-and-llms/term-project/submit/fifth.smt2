;; ===========================================================
;; File: eval_case10_helen_irene.smt2
;; SMT Check file for Fact Pattern 10: Helen & Irene (Ambiguous MSA Validity)
;; ===========================================================

(set-logic ALL)

;; --- START OF MODEL LOGIC ---
; --- Declare Sorts and Constants ---
(declare-sort Person)
(declare-const TP Person)
(declare-const PD Person)
; --- Declare Functions (Properties, Relationships, Thresholds) ---
(declare-fun Age (Person) Int)
(declare-fun GrossIncome (Person) Int)
(declare-fun IsStudent (Person) Bool)
(declare-fun IsPermanentlyTotallyDisabled (Person) Bool)
(declare-fun IsCitizenOrNationalOrResident (Person) Bool)
(declare-fun IsUSCitizenOrNational (Person) Bool)
(declare-fun IsChildOrDescendant (Person Person) Bool)
(declare-fun IsSiblingOrStepSibling (Person Person) Bool)
(declare-fun IsDescendantOfSiblingEtc (Person Person) Bool)
(declare-fun IsParentOrAncestor (Person Person) Bool)
(declare-fun IsStepParent (Person Person) Bool)
(declare-fun IsSiblingOfParent (Person Person) Bool)
(declare-fun IsChildOfSibling (Person Person) Bool)
(declare-fun IsInLaw (Person Person) Bool)
(declare-fun IsHouseholdMember (Person Person) Bool)
(declare-fun ResidesWithTPMoreThanHalfYear (Person Person) Bool)
(declare-fun HasSamePrincipalPlaceOfAbode (Person Person) Bool)
(declare-fun PDProvidesOverHalfOwnSupport (Person) Bool)
(declare-fun TPProvidesOverHalfSupport (Person Person) Bool)
(declare-fun HasMultipleSupportAgreement (Person Person) Bool) ; <-- The ambiguous predicate
(declare-fun FilesJointReturn (Person) Bool)
(declare-fun FilesJointReturnOnlyForRefund (Person) Bool)
(declare-fun IsDependentOfAnyTaxpayer (Person) Bool)
(declare-fun IsQC_OfAnyOtherTaxpayer (Person) Bool)
(declare-const ExemptionAmountThreshold Int)
(declare-fun IsAdoptedChildLivingWithUSCitizenTPHouseholdMember (Person Person) Bool)
; --- Define Helper Predicates ---
(define-fun QC_Relationship ((tp Person) (pd Person)) Bool (or (IsChildOrDescendant pd tp) (IsSiblingOrStepSibling pd tp) (IsDescendantOfSiblingEtc pd tp)))
(define-fun QC_AgeRequirement ((tp Person) (pd Person)) Bool (and (< (Age pd) (Age tp)) (or (IsPermanentlyTotallyDisabled pd) (< (Age pd) 19) (and (IsStudent pd) (< (Age pd) 24)))))
(define-fun QC_JointReturnTestFails ((pd Person)) Bool (and (FilesJointReturn pd) (not (FilesJointReturnOnlyForRefund pd))))
(define-fun QR_Relationship ((tp Person) (pd Person)) Bool (or (IsChildOrDescendant pd tp) (IsSiblingOrStepSibling pd tp) (IsParentOrAncestor pd tp) (IsStepParent pd tp) (IsChildOfSibling pd tp) (IsSiblingOfParent pd tp) (IsInLaw pd tp) (and (HasSamePrincipalPlaceOfAbode pd tp) (IsHouseholdMember pd tp))))
(define-fun QR_IncomeTest ((pd Person)) Bool (< (GrossIncome pd) ExemptionAmountThreshold))
(define-fun QR_SupportRequirement ((tp Person) (pd Person)) Bool (or (TPProvidesOverHalfSupport tp pd) (HasMultipleSupportAgreement tp pd))) ; Uses MSA
(define-fun Exception_Citizenship ((tp Person) (pd Person)) Bool (not (or (IsCitizenOrNationalOrResident pd) (IsAdoptedChildLivingWithUSCitizenTPHouseholdMember tp pd))))
(define-fun ExceptionApplies ((tp Person) (pd Person)) Bool (or (IsDependentOfAnyTaxpayer pd) (FilesJointReturn pd) (Exception_Citizenship tp pd)))
; --- Define Qualifying Child (QC) --- (c)
(define-fun IsQualifyingChild ((tp Person) (pd Person)) Bool
  (and (QC_Relationship tp pd)
       (ResidesWithTPMoreThanHalfYear tp pd)
       (QC_AgeRequirement tp pd)
       (not (PDProvidesOverHalfOwnSupport pd))
       (not (QC_JointReturnTestFails pd))
))
; --- Define Qualifying Relative (QR) --- (d)
(define-fun IsQualifyingRelative ((tp Person) (pd Person)) Bool
  (and (QR_Relationship tp pd)
       (QR_IncomeTest pd)
       (QR_SupportRequirement tp pd) ; <-- Depends on potentially ambiguous MSA
       (not (IsQualifyingChild tp pd))
       (not (IsQC_OfAnyOtherTaxpayer pd))
))
; --- Define Dependent (Overall) --- (a)
(define-fun IsDependent ((tp Person) (pd Person)) Bool
  (and (not (ExceptionApplies tp pd))
       (or (IsQualifyingChild tp pd)
           (IsQualifyingRelative tp pd) ; <-- Depends on QR, which depends on MSA
       )))
;; --- END OF MODEL LOGIC ---

;; --- Scenario Specific Declarations ---
(declare-const Helen Person)
(declare-const Irene Person)

;; --- Map TP/PD ---
(assert (= TP Helen))
(assert (= PD Irene))

;; --- Fact Assertions ---
(assert (= (Age Helen) 70))
(assert (= (Age Irene) 90))
(assert (IsUSCitizenOrNational Helen) )
(assert (IsUSCitizenOrNational Irene) )
(assert (IsCitizenOrNationalOrResident Irene) )

(assert (IsParentOrAncestor Irene Helen) ) ; Mother relationship

(assert (= (ResidesWithTPMoreThanHalfYear Helen Irene) false) ) ; Lives in nursing home
(assert (= (HasSamePrincipalPlaceOfAbode Irene Helen) false) )

(assert (= (GrossIncome Irene) 2000)) ; Below threshold

;; --- AMBIGUOUS SUPPORT / MSA ---
;; We know Helen provided 30% (not >50%), so TPProvidesOverHalfSupport is false
(assert (not (TPProvidesOverHalfSupport Helen Irene)) )
;; We know an MSA *might* exist, but the facts don't confirm it meets the legal requirements
;; (e.g., WRITTEN declaration by brothers not mentioned).
;; Therefore, we CANNOT definitively assert HasMultipleSupportAgreement is true.
;; We also cannot assert it's false, as the conditions might be met outside the facts given.
;; (assert (HasMultipleSupportAgreement Helen Irene)) ; <-- DO NOT ASSERT TRUE
;; (assert (not (HasMultipleSupportAgreement Helen Irene))) ; <-- DO NOT ASSERT FALSE

; Assume Irene doesn't provide her own support
(assert (= (PDProvidesOverHalfOwnSupport Irene) false) )

; Assume defaults for others
(assert (= (FilesJointReturn Irene) false) )
(assert (= (IsPermanentlyTotallyDisabled Irene) false) ) ; Not stated
(assert (= (IsQualifyingChild Helen Irene) false) ) ; Fails age/residency
(assert (= (IsQC_OfAnyOtherTaxpayer Irene) false) )
(assert (= (IsDependentOfAnyTaxpayer Irene) false))

;; --- Set Threshold ---
(assert (= ExemptionAmountThreshold 4700)) ; Irene's income is below

;; --- Check Dependency ---
(check-sat)
(get-value (IsDependent Helen Irene))
;; Expected Z3 Output: sat, but the value for IsDependent might be complex or
;; show dependency on the unassigned HasMultipleSupportAgreement, indicating UNKNOWN.