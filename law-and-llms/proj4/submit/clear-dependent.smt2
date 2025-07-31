; --- Include or paste model.smt2 definitions here ---
(set-logic ALL)
(declare-sort Person)

; --- Declare constants representing the main parties ---
; Generic placeholders
(declare-const TP Person)
(declare-const PD Person)

; Specific individuals for this scenario - DECLARE BEFORE USE
(declare-const Alice Person)
(declare-const Bob Person)

; --- Declare functions representing properties and relationships ---
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

; ... include define-fun blocks from model.smt2 ...
(define-fun QC_Relationship ((tp Person) (pd Person)) Bool (or (IsChildOrDescendant pd tp) (IsSiblingOrStepSibling pd tp) (IsDescendantOfSiblingEtc pd tp)))
(define-fun QC_AgeRequirement ((tp Person) (pd Person)) Bool (and (< (Age pd) (Age tp)) (or (IsPermanentlyTotallyDisabled pd) (< (Age pd) 19) (and (IsStudent pd) (< (Age pd) 24)))))
(define-fun QR_Relationship ((tp Person) (pd Person)) Bool (or (IsChildOrDescendant pd tp) (IsSiblingOrStepSibling pd tp) (IsParentOrAncestor pd tp) (IsStepParent pd tp) (IsChildOfSibling pd tp) (IsSiblingOfParent pd tp) (IsInLaw pd tp) (and (HasSamePrincipalPlaceOfAbode pd tp) (IsHouseholdMember pd tp))))
(define-fun QR_SupportRequirement ((tp Person) (pd Person)) Bool (or (TPProvidesOverHalfSupport tp pd) (HasMultipleSupportAgreement tp pd)))
(define-fun Exception_Citizenship ((tp Person) (pd Person)) Bool (not (or (IsCitizenOrNationalOrResident pd) (IsAdoptedChildLivingWithUSCitizenTPHouseholdMember tp pd))))
(define-fun Exception_DependentHasDependent ((pd Person)) Bool (IsDependentOfAnyTaxpayer pd))
(define-fun Exception_MarriedFilingJointly ((pd Person)) Bool (FilesJointReturn pd))
(define-fun ExceptionApplies ((tp Person) (pd Person)) Bool (or (Exception_DependentHasDependent pd) (Exception_MarriedFilingJointly pd) (Exception_Citizenship tp pd)))
(define-fun IsQualifyingChild ((tp Person) (pd Person)) Bool (and (QC_Relationship tp pd) (ResidesWithTPMoreThanHalfYear tp pd) (QC_AgeRequirement tp pd) (not (PDProvidesOverHalfOwnSupport pd)) (not (and (FilesJointReturn pd) (not (FilesJointReturnOnlyForRefund pd))))))
(define-fun IsQualifyingRelative ((tp Person) (pd Person)) Bool (and (QR_Relationship tp pd) (< (GrossIncome pd) ExemptionAmountThreshold) (QR_SupportRequirement tp pd) (not (IsQualifyingChild tp pd)) (not (IsQC_OfAnyOtherTaxpayer pd))))
(define-fun IsDependent ((tp Person) (pd Person)) Bool (and (not (ExceptionApplies tp pd)) (or (IsQualifyingChild tp pd) (IsQualifyingRelative tp pd))))

; --- Scenario 1 Assertions ---
; Assign generic TP/PD to specific individuals for this check
(assert (= TP Alice)) ; Alice is now known
(assert (= PD Bob))   ; Bob is now known

; Assert facts about Alice and Bob
(assert (= (Age Alice) 40))
(assert (= (Age Bob) 15))
(assert (IsCitizenOrNationalOrResident Alice))
(assert (IsCitizenOrNationalOrResident Bob))
(assert (IsUSCitizenOrNational Alice))

; Relationship
(assert (IsChildOrDescendant Bob Alice))
(assert (not (IsSiblingOrStepSibling Bob Alice)))
(assert (not (IsDescendantOfSiblingEtc Bob Alice)))
(assert (not (IsParentOrAncestor Bob Alice)))
(assert (not (IsStepParent Bob Alice)))
(assert (not (IsSiblingOfParent Bob Alice)))
(assert (not (IsChildOfSibling Bob Alice)))
(assert (not (IsInLaw Bob Alice)))
(assert (not (IsHouseholdMember Bob Alice))) ; Explicitly not just a household member for QR

; Residency
(assert (ResidesWithTPMoreThanHalfYear Alice Bob))
(assert (HasSamePrincipalPlaceOfAbode Bob Alice))

; Support
(assert (not (PDProvidesOverHalfOwnSupport Bob)))
(assert (TPProvidesOverHalfSupport Alice Bob))
(assert (not (HasMultipleSupportAgreement Alice Bob)))

; Income
(assert (= (GrossIncome Bob) 0))

; Filing Status / Other
(assert (not (FilesJointReturn Bob)))
(assert (not (FilesJointReturnOnlyForRefund Bob)))
(assert (not (IsDependentOfAnyTaxpayer Bob)))
(assert (not (IsQC_OfAnyOtherTaxpayer Bob)))

; Student/Disability Status
(assert (IsStudent Bob))
(assert (not (IsPermanentlyTotallyDisabled Bob)))

; Set Exemption Amount Threshold (example value)
(assert (= ExemptionAmountThreshold 4700))

; --- Check Dependency ---
(check-sat)
(echo "Scenario 1: Is Bob a dependent of Alice?")
(eval (IsDependent Alice Bob))
(echo "Is Bob a Qualifying Child of Alice?")
(eval (IsQualifyingChild Alice Bob))
(echo "Is Bob a Qualifying Relative of Alice?")
(eval (IsQualifyingRelative Alice Bob))
(echo "Do Exceptions Apply?")
(eval (ExceptionApplies Alice Bob))