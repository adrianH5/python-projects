; SMT-LIB 2 Translation of 26 USC 152(a)-(d) - Dependent Definition
; Simplified model focusing on core logic

(set-logic ALL) ; Using Bool, Int, and uninterpreted functions/sorts

; Declare a sort for persons
(declare-sort Person)

; --- Declare constants representing the main parties ---
; These would be replaced/instantiated in specific scenarios
(declare-const TP Person) ; Taxpayer
(declare-const PD Person) ; Potential Dependent

; --- Declare functions representing properties and relationships ---

; Basic Properties
(declare-fun Age (Person) Int)
(declare-fun GrossIncome (Person) Int) ; Representing gross income amount
(declare-fun IsStudent (Person) Bool)
(declare-fun IsPermanentlyTotallyDisabled (Person) Bool)
(declare-fun IsCitizenOrNationalOrResident (Person) Bool) ; Covers US citizen/national/resident of US/contiguous
(declare-fun IsUSCitizenOrNational (Person) Bool) ; Specifically for taxpayer in adoption exception

; Relationships (True if PD has the specified relationship to TP)
(declare-fun IsChildOrDescendant (Person Person) Bool) ; PD is child/descendant of TP
(declare-fun IsSiblingOrStepSibling (Person Person) Bool) ; PD is sibling/step-sibling of TP
(declare-fun IsDescendantOfSiblingEtc (Person Person) Bool) ; PD is descendant of TP's sibling/step-sibling
(declare-fun IsParentOrAncestor (Person Person) Bool) ; PD is parent/ancestor of TP
(declare-fun IsStepParent (Person Person) Bool) ; PD is step-parent of TP
(declare-fun IsSiblingOfParent (Person Person) Bool) ; PD is aunt/uncle of TP
(declare-fun IsChildOfSibling (Person Person) Bool) ; PD is niece/nephew of TP
(declare-fun IsInLaw (Person Person) Bool) ; PD is son/daughter/father/mother/brother/sister-in-law of TP
(declare-fun IsHouseholdMember (Person Person) Bool) ; PD lives with TP and is member of household (for (d)(2)(H) and (b)(3)(B))

; Residency
(declare-fun ResidesWithTPMoreThanHalfYear (Person Person) Bool) ; PD lived with TP > 1/2 year
(declare-fun HasSamePrincipalPlaceOfAbode (Person Person) Bool) ; For (b)(3)(B) and (d)(2)(H)

; Support
(declare-fun PDProvidesOverHalfOwnSupport (Person) Bool) ; PD provided > 1/2 their own support
(declare-fun TPProvidesOverHalfSupport (Person Person) Bool) ; TP provided > 1/2 of PD's support
(declare-fun HasMultipleSupportAgreement (Person Person) Bool) ; Simplified: True if TP is part of a valid MSA for PD meeting (d)(3) requirements

; Filing Status / Other Tax Rules
(declare-fun FilesJointReturn (Person) Bool) ; PD filed joint return with spouse
(declare-fun FilesJointReturnOnlyForRefund (Person) Bool) ; Special exception for QC joint return
(declare-fun IsDependentOfAnyTaxpayer (Person) Bool) ; If PD is claimed as dependent by someone else (for b(1))
(declare-fun IsQC_OfAnyOtherTaxpayer (Person) Bool) ; If PD is a QC of *another* taxpayer (for d(1)(D))

; Thresholds (simplified as constants)
(declare-const ExemptionAmountThreshold Int) ; The gross income limit for QR (d)(1)(B)

; Adoption Exception Helper (b)(3)(B)
(declare-fun IsAdoptedChildLivingWithUSCitizenTPHouseholdMember (Person Person) Bool)

; --- Define Helper Predicates for Clarity ---

; Helper for QC Relationship (c)(2)
(define-fun QC_Relationship ((tp Person) (pd Person)) Bool
  (or (IsChildOrDescendant pd tp)
      (IsSiblingOrStepSibling pd tp)
      (IsDescendantOfSiblingEtc pd tp)))

; Helper for QC Age Requirement (c)(3)
(define-fun QC_AgeRequirement ((tp Person) (pd Person)) Bool
  (and (< (Age pd) (Age tp)) ; Must be younger than taxpayer
       (or (IsPermanentlyTotallyDisabled pd)
           (< (Age pd) 19)
           (and (IsStudent pd) (< (Age pd) 24)))))

; Helper for QR Relationship (d)(2)
(define-fun QR_Relationship ((tp Person) (pd Person)) Bool
  (or (IsChildOrDescendant pd tp)
      (IsSiblingOrStepSibling pd tp)
      (IsParentOrAncestor pd tp)
      (IsStepParent pd tp)
      (IsChildOfSibling pd tp) ; niece/nephew
      (IsSiblingOfParent pd tp) ; aunt/uncle
      (IsInLaw pd tp)
      (and (HasSamePrincipalPlaceOfAbode pd tp) (IsHouseholdMember pd tp)))) ; Non-relative household member

; Helper for QR Support Requirement (d)(1)(C) + (d)(3)
(define-fun QR_SupportRequirement ((tp Person) (pd Person)) Bool
  (or (TPProvidesOverHalfSupport tp pd)
      (HasMultipleSupportAgreement tp pd))) ; Simplified MSA

; Helper for Exception (b)(3) - Citizenship/Residency
(define-fun Exception_Citizenship ((tp Person) (pd Person)) Bool
  (not (or (IsCitizenOrNationalOrResident pd)
           (IsAdoptedChildLivingWithUSCitizenTPHouseholdMember tp pd))))

; Helper for Exception (b)(1) - Dependent cannot have dependents (approximation)
; Note: The rule is subtle - if X is a dependent of Y for Y's tax year starting in Calendar Year Z,
; X has no dependents for X's tax year starting in Z. We simplify this.
(define-fun Exception_DependentHasDependent ((pd Person)) Bool
  (IsDependentOfAnyTaxpayer pd)) ; Simplified check

; Helper for Exception (b)(2) - Married filing jointly
(define-fun Exception_MarriedFilingJointly ((pd Person)) Bool
  (FilesJointReturn pd))

; Combined Exceptions (b)
(define-fun ExceptionApplies ((tp Person) (pd Person)) Bool
  (or (Exception_DependentHasDependent pd)
      (Exception_MarriedFilingJointly pd)
      (Exception_Citizenship tp pd)))

; --- Define Qualifying Child (QC) --- (c)
(define-fun IsQualifyingChild ((tp Person) (pd Person)) Bool
  (and (QC_Relationship tp pd)                             ; (c)(1)(A)
       (ResidesWithTPMoreThanHalfYear tp pd)             ; (c)(1)(B)
       (QC_AgeRequirement tp pd)                           ; (c)(1)(C)
       (not (PDProvidesOverHalfOwnSupport pd))             ; (c)(1)(D)
       (not (and (FilesJointReturn pd)                     ; (c)(1)(E)
                 (not (FilesJointReturnOnlyForRefund pd)))) ; (Handles joint return unless only for refund)
       ; Ignoring tie-breaker rules (c)(4) for simplicity
))

; --- Define Qualifying Relative (QR) --- (d)
(define-fun IsQualifyingRelative ((tp Person) (pd Person)) Bool
  (and (QR_Relationship tp pd)                             ; (d)(1)(A)
       (< (GrossIncome pd) ExemptionAmountThreshold)        ; (d)(1)(B) - Ignoring disability income exception (d)(4)
       (QR_SupportRequirement tp pd)                       ; (d)(1)(C) - Incorporates simplified MSA (d)(3)
       (not (IsQualifyingChild tp pd))                     ; (d)(1)(D) - Not a QC of this TP
       (not (IsQC_OfAnyOtherTaxpayer pd))                  ; (d)(1)(D) - Not a QC of any other taxpayer (simplified)
       ; Ignoring special support rules (d)(5) for simplicity
))

; --- Define Dependent (Overall) --- (a)
(define-fun IsDependent ((tp Person) (pd Person)) Bool
  (and (not (ExceptionApplies tp pd)) ; No exceptions apply (b)
       (or (IsQualifyingChild tp pd)  ; Is QC (c)
           (IsQualifyingRelative tp pd) ; Is QR (d)
       )))

; --- Basic Assertions/Checks ---
; Example: Assert that someone cannot be both QC and QR (implicitly handled by d(1)(D))
; (assert (forall ((tp Person) (pd Person)) (not (and (IsQualifyingChild tp pd) (IsQualifyingRelative tp pd))))) ; This should hold based on def of QR

; We will add scenario-specific asserts and checks in separate files or below this block.