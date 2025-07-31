;; ===========================================================
;; File: eval_case4_luis_paco.smt2
;; SMT Check file for Fact Pattern 4: Luis & Paco (QR Household Member?, Fails Income)
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
       (QR_IncomeTest pd) ; Fails here
       (QR_SupportRequirement tp pd)
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
(declare-const Luis Person)
(declare-const Paco Person)

;; --- Map TP/PD ---
(assert (= TP Luis))
(assert (= PD Paco))

;; --- Fact Assertions ---
(assert (= (Age Luis) 55))
(assert (= (Age Paco) 35))
(assert (IsUSCitizenOrNational Luis) )
(assert (IsUSCitizenOrNational Paco) )
(assert (IsCitizenOrNationalOrResident Paco) )

; Relationship: Cousin not listed, use household member rule
(assert (HasSamePrincipalPlaceOfAbode Paco Luis) ) ; Lived entire year
(assert (IsHouseholdMember Paco Luis) ) ; Assume member of household

(assert (ResidesWithTPMoreThanHalfYear Luis Paco) ) ; Implied by entire year

(assert (TPProvidesOverHalfSupport Luis Paco) ) ; 70%
(assert (= (PDProvidesOverHalfOwnSupport Paco) false) ) ; Implied

(assert (= (GrossIncome Paco) 8200)) ; Key QR failure
(assert (= (FilesJointReturn Paco) false) )
(assert (= (IsStudent Paco) false) )
(assert (= (IsPermanentlyTotallyDisabled Paco) false) )
(assert (= (IsQualifyingChild Luis Paco) false) )
(assert (= (IsQC_OfAnyOtherTaxpayer Paco) false) )
(assert (= (HasMultipleSupportAgreement Luis Paco) false) )
(assert (= (IsDependentOfAnyTaxpayer Paco) false))

;; --- Set Threshold ---
(assert (= ExemptionAmountThreshold 4700)) ; Paco's income is above

;; --- Check Dependency ---
(check-sat)
(get-value (IsDependent Luis Paco))