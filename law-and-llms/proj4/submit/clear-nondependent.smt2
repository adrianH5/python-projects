; --- Include or paste model.smt2 definitions here ---
(set-logic ALL)
(declare-sort Person)

; --- Declare constants representing the main parties ---
(declare-const TP Person)
(declare-const PD Person)

; Specific individuals for this scenario - DECLARE BEFORE USE
(declare-const Charles Person)
(declare-const Diane Person)

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

; --- Scenario 2 Assertions ---
(assert (= TP Charles)) ; Charles is now known
(assert (= PD Diane))   ; Diane is now known

; Assert facts about Charles and Diane
(assert (= (Age Charles) 50))
(assert (= (Age Diane) 48))
(assert (IsCitizenOrNationalOrResident Charles))
(assert (IsCitizenOrNationalOrResident Diane))
(assert (IsUSCitizenOrNational Charles))

; Relationship
(assert (not (IsChildOrDescendant Diane Charles)))
(assert (IsSiblingOrStepSibling Diane Charles))
(assert (not (IsDescendantOfSiblingEtc Diane Charles)))
(assert (not (IsParentOrAncestor Diane Charles)))
(assert (not (IsStepParent Diane Charles)))
(assert (not (IsSiblingOfParent Diane Charles)))
(assert (not (IsChildOfSibling Diane Charles)))
(assert (not (IsInLaw Diane Charles)))
(assert (not (IsHouseholdMember Diane Charles)))

; Residency
(assert (not (ResidesWithTPMoreThanHalfYear Charles Diane)))
(assert (not (HasSamePrincipalPlaceOfAbode Diane Charles)))

; Support
(assert (PDProvidesOverHalfOwnSupport Diane))
(assert (not (TPProvidesOverHalfSupport Charles Diane)))
(assert (not (HasMultipleSupportAgreement Charles Diane)))

; Income
(assert (= (GrossIncome Diane) 60000))

; Filing Status / Other
(assert (not (FilesJointReturn Diane)))
(assert (not (FilesJointReturnOnlyForRefund Diane)))
(assert (not (IsDependentOfAnyTaxpayer Diane)))
(assert (not (IsQC_OfAnyOtherTaxpayer Diane)))

; Student/Disability Status
(assert (not (IsStudent Diane)))
(assert (not (IsPermanentlyTotallyDisabled Diane)))

; Set Exemption Amount Threshold (example value)
(assert (= ExemptionAmountThreshold 4700))

; --- Check Dependency ---
(check-sat)
(echo "Scenario 2: Is Diane a dependent of Charles?")
(eval (IsDependent Charles Diane))
(echo "Is Diane a Qualifying Child of Charles?")
(eval (IsQualifyingChild Charles Diane))
(echo "Is Diane a Qualifying Relative of Charles?")
(eval (IsQualifyingRelative Charles Diane))
(echo "Do Exceptions Apply?")
(eval (ExceptionApplies Charles Diane))