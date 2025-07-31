; --- Include or paste model.smt2 definitions here ---
(set-logic ALL)
(declare-sort Person)

; --- Declare constants representing the main parties ---
(declare-const TP Person)
(declare-const PD Person)

; Specific individuals for this scenario - DECLARE BEFORE USE
(declare-const Eve Person)
(declare-const Frank Person)

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

; --- Scenario 3 Assertions ---
(assert (= TP Eve))     ; Eve is now known
(assert (= PD Frank))   ; Frank is now known

; Assert facts about Eve and Frank
(assert (= (Age Eve) 60))
(assert (= (Age Frank) 80))
(assert (IsCitizenOrNationalOrResident Eve))
(assert (IsCitizenOrNationalOrResident Frank))
(assert (IsUSCitizenOrNational Eve))

; Relationship
(assert (not (IsChildOrDescendant Frank Eve)))
(assert (IsParentOrAncestor Frank Eve))
(assert (not (IsSiblingOrStepSibling Frank Eve)))
(assert (not (IsDescendantOfSiblingEtc Frank Eve)))
(assert (not (IsStepParent Frank Eve)))
(assert (not (IsSiblingOfParent Frank Eve)))
(assert (not (IsChildOfSibling Frank Eve)))
(assert (not (IsInLaw Frank Eve)))
(assert (not (IsHouseholdMember Frank Eve)))


; Residency
(assert (not (ResidesWithTPMoreThanHalfYear Eve Frank)))
(assert (not (HasSamePrincipalPlaceOfAbode Frank Eve)))

; Support
(assert (not (PDProvidesOverHalfOwnSupport Frank)))
(assert (TPProvidesOverHalfSupport Eve Frank))
(assert (not (HasMultipleSupportAgreement Eve Frank)))

; Income
(assert (= (GrossIncome Frank) 4800))

; Filing Status / Other
(assert (not (FilesJointReturn Frank)))
(assert (not (FilesJointReturnOnlyForRefund Frank)))
(assert (not (IsDependentOfAnyTaxpayer Frank)))
(assert (not (IsQC_OfAnyOtherTaxpayer Frank)))

; Student/Disability Status
(assert (not (IsStudent Frank)))
(assert (not (IsPermanentlyTotallyDisabled Frank)))

; Set Exemption Amount Threshold (example value)
(assert (= ExemptionAmountThreshold 4700))

; --- Check Dependency ---
(check-sat)
(echo "Scenario 3: Is Frank a dependent of Eve?")
(eval (IsDependent Eve Frank))
(echo "Is Frank a Qualifying Child of Eve?")
(eval (IsQualifyingChild Eve Frank))
(echo "Is Frank a Qualifying Relative of Eve?")
(eval (IsQualifyingRelative Eve Frank))
(echo "Does Frank meet the QR Gross Income Test?")
(eval (< (GrossIncome Frank) ExemptionAmountThreshold))
(echo "Do Exceptions Apply?")
(eval (ExceptionApplies Eve Frank))