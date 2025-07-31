;; ===========================================================
;; File: eval_case1_marcus_lily.smt2
;; SMT Check file for Fact Pattern 1: Marcus & Lily (QC Student)
;; ===========================================================

(set-logic ALL)

;; --- START OF MODEL LOGIC ---
; --- Declare Sorts and Constants ---
(declare-sort Person)
(declare-const TP Person) ; Generic Taxpayer placeholder
(declare-const PD Person) ; Generic Potential Dependent placeholder

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
       (QR_SupportRequirement tp pd)
       (not (IsQualifyingChild tp pd))
       (not (IsQC_OfAnyOtherTaxpayer pd))
))

; --- Define Dependent (Overall) --- (a) *** CORRECT SINGLE DEFINITION ***
(define-fun IsDependent ((tp Person) (pd Person)) Bool
  (and (not (ExceptionApplies tp pd))
       (or (IsQualifyingChild tp pd)
           (IsQualifyingRelative tp pd)
       )))
;; --- END OF MODEL LOGIC ---

;; --- Scenario Specific Declarations ---
(declare-const Marcus Person)
(declare-const Lily Person)

;; --- Map TP/PD ---
(assert (= TP Marcus))
(assert (= PD Lily))

;; --- Fact Assertions ---
(assert (= (Age Marcus) 48))
(assert (= (Age Lily) 23))
(assert (IsUSCitizenOrNational Marcus) )
(assert (IsUSCitizenOrNational Lily) )
(assert (IsCitizenOrNationalOrResident Lily) )

(assert (IsChildOrDescendant Lily Marcus) )
(assert (IsStudent Lily) )
(assert (ResidesWithTPMoreThanHalfYear Marcus Lily) )
(assert (TPProvidesOverHalfSupport Marcus Lily) )
(assert (= (PDProvidesOverHalfOwnSupport Lily) false) )
(assert (= (GrossIncome Lily) 3200))
(assert (= (FilesJointReturn Lily) false) )
(assert (= (IsPermanentlyTotallyDisabled Lily) false) )
(assert (= (IsDependentOfAnyTaxpayer Lily) false) )
(assert (= (IsQC_OfAnyOtherTaxpayer Lily) false) )
(assert (= (HasMultipleSupportAgreement Marcus Lily) false))

;; --- Set Threshold ---
(assert (= ExemptionAmountThreshold 4700))

;; --- Check Dependency ---
(check-sat)
(get-value (IsDependent Marcus Lily))