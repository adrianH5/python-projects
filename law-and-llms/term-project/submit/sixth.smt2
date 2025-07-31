;; ===========================================================
;; File: eval_case7_brenda_carl.smt2
;; SMT Check file for Ambiguous Fact Pattern 7: Brenda & Carl (Ambiguous Support)
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
(declare-fun TPProvidesOverHalfSupport (Person Person) Bool) ; Intentionally NOT asserted below
(declare-fun HasMultipleSupportAgreement (Person Person) Bool)
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
(define-fun QR_SupportRequirement ((tp Person) (pd Person)) Bool (or (TPProvidesOverHalfSupport tp pd) (HasMultipleSupportAgreement tp pd)))
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
       (QR_SupportRequirement tp pd) ; Depends on TPProvidesOverHalfSupport which is unasserted
       (not (IsQualifyingChild tp pd))
       (not (IsQC_OfAnyOtherTaxpayer pd))
))
; --- Define Dependent (Overall) --- (a)
(define-fun IsDependent ((tp Person) (pd Person)) Bool
  (and (not (ExceptionApplies tp pd))
       (or (IsQualifyingChild tp pd)
           (IsQualifyingRelative tp pd)
       )))
;; --- END OF MODEL LOGIC ---

;; --- Scenario Specific Declarations ---
(declare-const Brenda Person)
(declare-const Carl Person)

;; --- Map TP/PD ---
(assert (= TP Brenda))
(assert (= PD Carl))

;; --- Fact Assertions ---
(assert (= (Age Brenda) 65))
(assert (= (Age Carl) 85))
(assert (IsUSCitizenOrNational Brenda) )
(assert (IsUSCitizenOrNational Carl) )
(assert (IsCitizenOrNationalOrResident Carl) )

(assert (IsParentOrAncestor Carl Brenda) ) ; Father

(assert (= (ResidesWithTPMoreThanHalfYear Brenda Carl) false) ) ; Lives separately
(assert (= (HasSamePrincipalPlaceOfAbode Carl Brenda) false))

(assert (= (GrossIncome Carl) 4000)) ; Below threshold

; Support is ambiguous - DO NOT ASSERT TPProvidesOverHalfSupport
; We can assert Carl didn't provide his own, as his income is low relative to likely costs
(assert (= (PDProvidesOverHalfOwnSupport Carl) false) )

(assert (= (FilesJointReturn Carl) false) )
(assert (= (IsPermanentlyTotallyDisabled Carl) false) )
(assert (= (IsQualifyingChild Brenda Carl) false) )
(assert (= (IsQC_OfAnyOtherTaxpayer Carl) false) )
(assert (= (IsDependentOfAnyTaxpayer Carl) false) )
(assert (= (HasMultipleSupportAgreement Brenda Carl) false)) ; No mention of MSA

;; --- Set Threshold ---
(assert (= ExemptionAmountThreshold 4700))

;; --- Check Dependency ---
;; We expect this to be SAT because a model exists where TPProvides > 50% is false, making IsDependent false.
;; And another model exists where TPProvides > 50% is true, making IsDependent true.
;; Z3 might return one specific model, but the status is truly ambiguous.
(check-sat)
(get-value (IsDependent Brenda Carl))
;; To confirm ambiguity, you could try asserting the opposite and check-sat again,
;; or use more advanced SMT techniques if needed, but for this project,
;; recognizing the missing assertion maps to "Unknown" is sufficient.