// DO_NOT_CHECK_SYMBOL_RESTORE

// class: java/lang/String

// RESULT
/*
KtFirJavaFieldSymbol:
  annotatedType: [] ft<kotlin/CharArray, kotlin/CharArray?>
  callableIdIfNonLocal: java/lang/String.value
  isExtension: false
  isStatic: false
  isVal: true
  modality: FINAL
  name: value
  origin: JAVA
  receiverType: null
  symbolKind: MEMBER
  visibility: Private

KtFirJavaFieldSymbol:
  annotatedType: [] kotlin/Int
  callableIdIfNonLocal: java/lang/String.hash
  isExtension: false
  isStatic: false
  isVal: false
  modality: OPEN
  name: hash
  origin: JAVA
  receiverType: null
  symbolKind: MEMBER
  visibility: Private

KtFirFunctionSymbol:
  annotatedType: [] kotlin/Int
  annotationClassIds: []
  annotations: []
  callableIdIfNonLocal: java/lang/String.hash32
  dispatchType: java/lang/String
  hasStableParameterNames: false
  isExtension: false
  isExternal: false
  isInfix: false
  isInline: false
  isOperator: false
  isOverride: false
  isStatic: false
  isSuspend: false
  modality: OPEN
  name: hash32
  origin: JAVA
  receiverType: null
  symbolKind: MEMBER
  typeParameters: []
  valueParameters: []
  visibility: PackageVisibility

KtFirJavaFieldSymbol:
  annotatedType: [] kotlin/Int
  callableIdIfNonLocal: java/lang/String.hash32
  isExtension: false
  isStatic: false
  isVal: false
  modality: OPEN
  name: hash32
  origin: JAVA
  receiverType: null
  symbolKind: MEMBER
  visibility: Private

KtFirSyntheticJavaPropertySymbol:
  annotatedType: [] kotlin/Int
  annotationClassIds: []
  annotations: []
  callableIdIfNonLocal: java/lang/String.length
  dispatchType: java/lang/String
  getter: KtFirPropertyGetterSymbol(<getter>)
  hasBackingField: true
  hasGetter: true
  hasSetter: false
  initializer: null
  isExtension: false
  isOverride: false
  isStatic: false
  isVal: true
  javaGetterName: length
  javaSetterName: null
  modality: OPEN
  name: length
  origin: JAVA_SYNTHETIC_PROPERTY
  receiverType: null
  setter: null
  symbolKind: MEMBER
  visibility: Public

KtFirFunctionSymbol:
  annotatedType: [] kotlin/Boolean
  annotationClassIds: []
  annotations: []
  callableIdIfNonLocal: java/lang/String.isEmpty
  dispatchType: java/lang/String
  hasStableParameterNames: false
  isExtension: false
  isExternal: false
  isInfix: false
  isInline: false
  isOperator: false
  isOverride: false
  isStatic: false
  isSuspend: false
  modality: OPEN
  name: isEmpty
  origin: JAVA
  receiverType: null
  symbolKind: MEMBER
  typeParameters: []
  valueParameters: []
  visibility: Public

KtFirFunctionSymbol:
  annotatedType: [] kotlin/Char
  annotationClassIds: []
  annotations: []
  callableIdIfNonLocal: java/lang/String.charAt
  dispatchType: java/lang/String
  hasStableParameterNames: false
  isExtension: false
  isExternal: false
  isInfix: false
  isInline: false
  isOperator: false
  isOverride: false
  isStatic: false
  isSuspend: false
  modality: OPEN
  name: charAt
  origin: JAVA
  receiverType: null
  symbolKind: MEMBER
  typeParameters: []
  valueParameters: [
    KtFirValueParameterSymbol(p0)
  ]
  visibility: Public

KtFirFunctionSymbol:
  annotatedType: [] kotlin/Int
  annotationClassIds: []
  annotations: []
  callableIdIfNonLocal: java/lang/String.codePointAt
  dispatchType: java/lang/String
  hasStableParameterNames: false
  isExtension: false
  isExternal: false
  isInfix: false
  isInline: false
  isOperator: false
  isOverride: false
  isStatic: false
  isSuspend: false
  modality: OPEN
  name: codePointAt
  origin: JAVA
  receiverType: null
  symbolKind: MEMBER
  typeParameters: []
  valueParameters: [
    KtFirValueParameterSymbol(p0)
  ]
  visibility: Public

KtFirFunctionSymbol:
  annotatedType: [] kotlin/Int
  annotationClassIds: []
  annotations: []
  callableIdIfNonLocal: java/lang/String.codePointBefore
  dispatchType: java/lang/String
  hasStableParameterNames: false
  isExtension: false
  isExternal: false
  isInfix: false
  isInline: false
  isOperator: false
  isOverride: false
  isStatic: false
  isSuspend: false
  modality: OPEN
  name: codePointBefore
  origin: JAVA
  receiverType: null
  symbolKind: MEMBER
  typeParameters: []
  valueParameters: [
    KtFirValueParameterSymbol(p0)
  ]
  visibility: Public

KtFirFunctionSymbol:
  annotatedType: [] kotlin/Int
  annotationClassIds: []
  annotations: []
  callableIdIfNonLocal: java/lang/String.codePointCount
  dispatchType: java/lang/String
  hasStableParameterNames: false
  isExtension: false
  isExternal: false
  isInfix: false
  isInline: false
  isOperator: false
  isOverride: false
  isStatic: false
  isSuspend: false
  modality: OPEN
  name: codePointCount
  origin: JAVA
  receiverType: null
  symbolKind: MEMBER
  typeParameters: []
  valueParameters: [
    KtFirValueParameterSymbol(p0)
    KtFirValueParameterSymbol(p1)
  ]
  visibility: Public

KtFirFunctionSymbol:
  annotatedType: [] kotlin/Int
  annotationClassIds: []
  annotations: []
  callableIdIfNonLocal: java/lang/String.offsetByCodePoints
  dispatchType: java/lang/String
  hasStableParameterNames: false
  isExtension: false
  isExternal: false
  isInfix: false
  isInline: false
  isOperator: false
  isOverride: false
  isStatic: false
  isSuspend: false
  modality: OPEN
  name: offsetByCodePoints
  origin: JAVA
  receiverType: null
  symbolKind: MEMBER
  typeParameters: []
  valueParameters: [
    KtFirValueParameterSymbol(p0)
    KtFirValueParameterSymbol(p1)
  ]
  visibility: Public

KtFirFunctionSymbol:
  annotatedType: [] kotlin/Unit
  annotationClassIds: []
  annotations: []
  callableIdIfNonLocal: java/lang/String.getChars
  dispatchType: java/lang/String
  hasStableParameterNames: false
  isExtension: false
  isExternal: false
  isInfix: false
  isInline: false
  isOperator: false
  isOverride: false
  isStatic: false
  isSuspend: false
  modality: OPEN
  name: getChars
  origin: JAVA
  receiverType: null
  symbolKind: MEMBER
  typeParameters: []
  valueParameters: [
    KtFirValueParameterSymbol(p0)
    KtFirValueParameterSymbol(p1)
  ]
  visibility: PackageVisibility

KtFirFunctionSymbol:
  annotatedType: [] kotlin/Unit
  annotationClassIds: []
  annotations: []
  callableIdIfNonLocal: java/lang/String.getChars
  dispatchType: java/lang/String
  hasStableParameterNames: false
  isExtension: false
  isExternal: false
  isInfix: false
  isInline: false
  isOperator: false
  isOverride: false
  isStatic: false
  isSuspend: false
  modality: OPEN
  name: getChars
  origin: JAVA
  receiverType: null
  symbolKind: MEMBER
  typeParameters: []
  valueParameters: [
    KtFirValueParameterSymbol(p0)
    KtFirValueParameterSymbol(p1)
    KtFirValueParameterSymbol(p2)
    KtFirValueParameterSymbol(p3)
  ]
  visibility: Public

KtFirFunctionSymbol:
  annotatedType: [] kotlin/Unit
  annotationClassIds: [
    kotlin/Deprecated
  ]
  annotations: [
    kotlin/Deprecated(message = Deprecated in Java)
      psi: null
  ]
  callableIdIfNonLocal: java/lang/String.getBytes
  dispatchType: java/lang/String
  hasStableParameterNames: false
  isExtension: false
  isExternal: false
  isInfix: false
  isInline: false
  isOperator: false
  isOverride: false
  isStatic: false
  isSuspend: false
  modality: OPEN
  name: getBytes
  origin: JAVA
  receiverType: null
  symbolKind: MEMBER
  typeParameters: []
  valueParameters: [
    KtFirValueParameterSymbol(p0)
    KtFirValueParameterSymbol(p1)
    KtFirValueParameterSymbol(p2)
    KtFirValueParameterSymbol(p3)
  ]
  visibility: Public

KtFirFunctionSymbol:
  annotatedType: [] ft<kotlin/ByteArray, kotlin/ByteArray?>
  annotationClassIds: []
  annotations: []
  callableIdIfNonLocal: java/lang/String.getBytes
  dispatchType: java/lang/String
  hasStableParameterNames: false
  isExtension: false
  isExternal: false
  isInfix: false
  isInline: false
  isOperator: false
  isOverride: false
  isStatic: false
  isSuspend: false
  modality: OPEN
  name: getBytes
  origin: JAVA
  receiverType: null
  symbolKind: MEMBER
  typeParameters: []
  valueParameters: [
    KtFirValueParameterSymbol(p0)
  ]
  visibility: Public

KtFirFunctionSymbol:
  annotatedType: [] ft<kotlin/ByteArray, kotlin/ByteArray?>
  annotationClassIds: []
  annotations: []
  callableIdIfNonLocal: java/lang/String.getBytes
  dispatchType: java/lang/String
  hasStableParameterNames: false
  isExtension: false
  isExternal: false
  isInfix: false
  isInline: false
  isOperator: false
  isOverride: false
  isStatic: false
  isSuspend: false
  modality: OPEN
  name: getBytes
  origin: JAVA
  receiverType: null
  symbolKind: MEMBER
  typeParameters: []
  valueParameters: [
    KtFirValueParameterSymbol(p0)
  ]
  visibility: Public

KtFirFunctionSymbol:
  annotatedType: [] ft<kotlin/ByteArray, kotlin/ByteArray?>
  annotationClassIds: []
  annotations: []
  callableIdIfNonLocal: java/lang/String.getBytes
  dispatchType: java/lang/String
  hasStableParameterNames: false
  isExtension: false
  isExternal: false
  isInfix: false
  isInline: false
  isOperator: false
  isOverride: false
  isStatic: false
  isSuspend: false
  modality: OPEN
  name: getBytes
  origin: JAVA
  receiverType: null
  symbolKind: MEMBER
  typeParameters: []
  valueParameters: []
  visibility: Public

KtFirFunctionSymbol:
  annotatedType: [] kotlin/Boolean
  annotationClassIds: []
  annotations: []
  callableIdIfNonLocal: java/lang/String.equals
  dispatchType: java/lang/String
  hasStableParameterNames: false
  isExtension: false
  isExternal: false
  isInfix: false
  isInline: false
  isOperator: true
  isOverride: false
  isStatic: false
  isSuspend: false
  modality: OPEN
  name: equals
  origin: JAVA
  receiverType: null
  symbolKind: MEMBER
  typeParameters: []
  valueParameters: [
    KtFirValueParameterSymbol(p0)
  ]
  visibility: Public

KtFirFunctionSymbol:
  annotatedType: [] kotlin/Boolean
  annotationClassIds: []
  annotations: []
  callableIdIfNonLocal: java/lang/String.contentEquals
  dispatchType: java/lang/String
  hasStableParameterNames: false
  isExtension: false
  isExternal: false
  isInfix: false
  isInline: false
  isOperator: false
  isOverride: false
  isStatic: false
  isSuspend: false
  modality: OPEN
  name: contentEquals
  origin: JAVA
  receiverType: null
  symbolKind: MEMBER
  typeParameters: []
  valueParameters: [
    KtFirValueParameterSymbol(p0)
  ]
  visibility: Public

KtFirFunctionSymbol:
  annotatedType: [] kotlin/Boolean
  annotationClassIds: []
  annotations: []
  callableIdIfNonLocal: java/lang/String.contentEquals
  dispatchType: java/lang/String
  hasStableParameterNames: false
  isExtension: false
  isExternal: false
  isInfix: false
  isInline: false
  isOperator: false
  isOverride: false
  isStatic: false
  isSuspend: false
  modality: OPEN
  name: contentEquals
  origin: JAVA
  receiverType: null
  symbolKind: MEMBER
  typeParameters: []
  valueParameters: [
    KtFirValueParameterSymbol(p0)
  ]
  visibility: Public

KtFirFunctionSymbol:
  annotatedType: [] kotlin/Boolean
  annotationClassIds: []
  annotations: []
  callableIdIfNonLocal: java/lang/String.equalsIgnoreCase
  dispatchType: java/lang/String
  hasStableParameterNames: false
  isExtension: false
  isExternal: false
  isInfix: false
  isInline: false
  isOperator: false
  isOverride: false
  isStatic: false
  isSuspend: false
  modality: OPEN
  name: equalsIgnoreCase
  origin: JAVA
  receiverType: null
  symbolKind: MEMBER
  typeParameters: []
  valueParameters: [
    KtFirValueParameterSymbol(p0)
  ]
  visibility: Public

KtFirFunctionSymbol:
  annotatedType: [] kotlin/Int
  annotationClassIds: []
  annotations: []
  callableIdIfNonLocal: java/lang/String.compareTo
  dispatchType: java/lang/String
  hasStableParameterNames: false
  isExtension: false
  isExternal: false
  isInfix: false
  isInline: false
  isOperator: true
  isOverride: false
  isStatic: false
  isSuspend: false
  modality: OPEN
  name: compareTo
  origin: JAVA
  receiverType: null
  symbolKind: MEMBER
  typeParameters: []
  valueParameters: [
    KtFirValueParameterSymbol(p0)
  ]
  visibility: Public

KtFirFunctionSymbol:
  annotatedType: [] kotlin/Int
  annotationClassIds: []
  annotations: []
  callableIdIfNonLocal: java/lang/String.compareToIgnoreCase
  dispatchType: java/lang/String
  hasStableParameterNames: false
  isExtension: false
  isExternal: false
  isInfix: false
  isInline: false
  isOperator: false
  isOverride: false
  isStatic: false
  isSuspend: false
  modality: OPEN
  name: compareToIgnoreCase
  origin: JAVA
  receiverType: null
  symbolKind: MEMBER
  typeParameters: []
  valueParameters: [
    KtFirValueParameterSymbol(p0)
  ]
  visibility: Public

KtFirFunctionSymbol:
  annotatedType: [] kotlin/Boolean
  annotationClassIds: []
  annotations: []
  callableIdIfNonLocal: java/lang/String.regionMatches
  dispatchType: java/lang/String
  hasStableParameterNames: false
  isExtension: false
  isExternal: false
  isInfix: false
  isInline: false
  isOperator: false
  isOverride: false
  isStatic: false
  isSuspend: false
  modality: OPEN
  name: regionMatches
  origin: JAVA
  receiverType: null
  symbolKind: MEMBER
  typeParameters: []
  valueParameters: [
    KtFirValueParameterSymbol(p0)
    KtFirValueParameterSymbol(p1)
    KtFirValueParameterSymbol(p2)
    KtFirValueParameterSymbol(p3)
  ]
  visibility: Public

KtFirFunctionSymbol:
  annotatedType: [] kotlin/Boolean
  annotationClassIds: []
  annotations: []
  callableIdIfNonLocal: java/lang/String.regionMatches
  dispatchType: java/lang/String
  hasStableParameterNames: false
  isExtension: false
  isExternal: false
  isInfix: false
  isInline: false
  isOperator: false
  isOverride: false
  isStatic: false
  isSuspend: false
  modality: OPEN
  name: regionMatches
  origin: JAVA
  receiverType: null
  symbolKind: MEMBER
  typeParameters: []
  valueParameters: [
    KtFirValueParameterSymbol(p0)
    KtFirValueParameterSymbol(p1)
    KtFirValueParameterSymbol(p2)
    KtFirValueParameterSymbol(p3)
    KtFirValueParameterSymbol(p4)
  ]
  visibility: Public

KtFirFunctionSymbol:
  annotatedType: [] kotlin/Boolean
  annotationClassIds: []
  annotations: []
  callableIdIfNonLocal: java/lang/String.startsWith
  dispatchType: java/lang/String
  hasStableParameterNames: false
  isExtension: false
  isExternal: false
  isInfix: false
  isInline: false
  isOperator: false
  isOverride: false
  isStatic: false
  isSuspend: false
  modality: OPEN
  name: startsWith
  origin: JAVA
  receiverType: null
  symbolKind: MEMBER
  typeParameters: []
  valueParameters: [
    KtFirValueParameterSymbol(p0)
    KtFirValueParameterSymbol(p1)
  ]
  visibility: Public

KtFirFunctionSymbol:
  annotatedType: [] kotlin/Boolean
  annotationClassIds: []
  annotations: []
  callableIdIfNonLocal: java/lang/String.startsWith
  dispatchType: java/lang/String
  hasStableParameterNames: false
  isExtension: false
  isExternal: false
  isInfix: false
  isInline: false
  isOperator: false
  isOverride: false
  isStatic: false
  isSuspend: false
  modality: OPEN
  name: startsWith
  origin: JAVA
  receiverType: null
  symbolKind: MEMBER
  typeParameters: []
  valueParameters: [
    KtFirValueParameterSymbol(p0)
  ]
  visibility: Public

KtFirFunctionSymbol:
  annotatedType: [] kotlin/Boolean
  annotationClassIds: []
  annotations: []
  callableIdIfNonLocal: java/lang/String.endsWith
  dispatchType: java/lang/String
  hasStableParameterNames: false
  isExtension: false
  isExternal: false
  isInfix: false
  isInline: false
  isOperator: false
  isOverride: false
  isStatic: false
  isSuspend: false
  modality: OPEN
  name: endsWith
  origin: JAVA
  receiverType: null
  symbolKind: MEMBER
  typeParameters: []
  valueParameters: [
    KtFirValueParameterSymbol(p0)
  ]
  visibility: Public

KtFirFunctionSymbol:
  annotatedType: [] kotlin/Int
  annotationClassIds: []
  annotations: []
  callableIdIfNonLocal: java/lang/String.hashCode
  dispatchType: java/lang/String
  hasStableParameterNames: false
  isExtension: false
  isExternal: false
  isInfix: false
  isInline: false
  isOperator: false
  isOverride: false
  isStatic: false
  isSuspend: false
  modality: OPEN
  name: hashCode
  origin: JAVA
  receiverType: null
  symbolKind: MEMBER
  typeParameters: []
  valueParameters: []
  visibility: Public

KtFirFunctionSymbol:
  annotatedType: [] kotlin/Int
  annotationClassIds: []
  annotations: []
  callableIdIfNonLocal: java/lang/String.indexOf
  dispatchType: java/lang/String
  hasStableParameterNames: false
  isExtension: false
  isExternal: false
  isInfix: false
  isInline: false
  isOperator: false
  isOverride: false
  isStatic: false
  isSuspend: false
  modality: OPEN
  name: indexOf
  origin: JAVA
  receiverType: null
  symbolKind: MEMBER
  typeParameters: []
  valueParameters: [
    KtFirValueParameterSymbol(p0)
  ]
  visibility: Public

KtFirFunctionSymbol:
  annotatedType: [] kotlin/Int
  annotationClassIds: []
  annotations: []
  callableIdIfNonLocal: java/lang/String.indexOf
  dispatchType: java/lang/String
  hasStableParameterNames: false
  isExtension: false
  isExternal: false
  isInfix: false
  isInline: false
  isOperator: false
  isOverride: false
  isStatic: false
  isSuspend: false
  modality: OPEN
  name: indexOf
  origin: JAVA
  receiverType: null
  symbolKind: MEMBER
  typeParameters: []
  valueParameters: [
    KtFirValueParameterSymbol(p0)
    KtFirValueParameterSymbol(p1)
  ]
  visibility: Public

KtFirFunctionSymbol:
  annotatedType: [] kotlin/Int
  annotationClassIds: []
  annotations: []
  callableIdIfNonLocal: java/lang/String.indexOf
  dispatchType: java/lang/String
  hasStableParameterNames: false
  isExtension: false
  isExternal: false
  isInfix: false
  isInline: false
  isOperator: false
  isOverride: false
  isStatic: false
  isSuspend: false
  modality: OPEN
  name: indexOf
  origin: JAVA
  receiverType: null
  symbolKind: MEMBER
  typeParameters: []
  valueParameters: [
    KtFirValueParameterSymbol(p0)
  ]
  visibility: Public

KtFirFunctionSymbol:
  annotatedType: [] kotlin/Int
  annotationClassIds: []
  annotations: []
  callableIdIfNonLocal: java/lang/String.indexOf
  dispatchType: java/lang/String
  hasStableParameterNames: false
  isExtension: false
  isExternal: false
  isInfix: false
  isInline: false
  isOperator: false
  isOverride: false
  isStatic: false
  isSuspend: false
  modality: OPEN
  name: indexOf
  origin: JAVA
  receiverType: null
  symbolKind: MEMBER
  typeParameters: []
  valueParameters: [
    KtFirValueParameterSymbol(p0)
    KtFirValueParameterSymbol(p1)
  ]
  visibility: Public

KtFirFunctionSymbol:
  annotatedType: [] kotlin/Int
  annotationClassIds: []
  annotations: []
  callableIdIfNonLocal: java/lang/String.indexOfSupplementary
  dispatchType: java/lang/String
  hasStableParameterNames: false
  isExtension: false
  isExternal: false
  isInfix: false
  isInline: false
  isOperator: false
  isOverride: false
  isStatic: false
  isSuspend: false
  modality: OPEN
  name: indexOfSupplementary
  origin: JAVA
  receiverType: null
  symbolKind: MEMBER
  typeParameters: []
  valueParameters: [
    KtFirValueParameterSymbol(p0)
    KtFirValueParameterSymbol(p1)
  ]
  visibility: Private

KtFirFunctionSymbol:
  annotatedType: [] kotlin/Int
  annotationClassIds: []
  annotations: []
  callableIdIfNonLocal: java/lang/String.lastIndexOf
  dispatchType: java/lang/String
  hasStableParameterNames: false
  isExtension: false
  isExternal: false
  isInfix: false
  isInline: false
  isOperator: false
  isOverride: false
  isStatic: false
  isSuspend: false
  modality: OPEN
  name: lastIndexOf
  origin: JAVA
  receiverType: null
  symbolKind: MEMBER
  typeParameters: []
  valueParameters: [
    KtFirValueParameterSymbol(p0)
  ]
  visibility: Public

KtFirFunctionSymbol:
  annotatedType: [] kotlin/Int
  annotationClassIds: []
  annotations: []
  callableIdIfNonLocal: java/lang/String.lastIndexOf
  dispatchType: java/lang/String
  hasStableParameterNames: false
  isExtension: false
  isExternal: false
  isInfix: false
  isInline: false
  isOperator: false
  isOverride: false
  isStatic: false
  isSuspend: false
  modality: OPEN
  name: lastIndexOf
  origin: JAVA
  receiverType: null
  symbolKind: MEMBER
  typeParameters: []
  valueParameters: [
    KtFirValueParameterSymbol(p0)
    KtFirValueParameterSymbol(p1)
  ]
  visibility: Public

KtFirFunctionSymbol:
  annotatedType: [] kotlin/Int
  annotationClassIds: []
  annotations: []
  callableIdIfNonLocal: java/lang/String.lastIndexOf
  dispatchType: java/lang/String
  hasStableParameterNames: false
  isExtension: false
  isExternal: false
  isInfix: false
  isInline: false
  isOperator: false
  isOverride: false
  isStatic: false
  isSuspend: false
  modality: OPEN
  name: lastIndexOf
  origin: JAVA
  receiverType: null
  symbolKind: MEMBER
  typeParameters: []
  valueParameters: [
    KtFirValueParameterSymbol(p0)
  ]
  visibility: Public

KtFirFunctionSymbol:
  annotatedType: [] kotlin/Int
  annotationClassIds: []
  annotations: []
  callableIdIfNonLocal: java/lang/String.lastIndexOf
  dispatchType: java/lang/String
  hasStableParameterNames: false
  isExtension: false
  isExternal: false
  isInfix: false
  isInline: false
  isOperator: false
  isOverride: false
  isStatic: false
  isSuspend: false
  modality: OPEN
  name: lastIndexOf
  origin: JAVA
  receiverType: null
  symbolKind: MEMBER
  typeParameters: []
  valueParameters: [
    KtFirValueParameterSymbol(p0)
    KtFirValueParameterSymbol(p1)
  ]
  visibility: Public

KtFirFunctionSymbol:
  annotatedType: [] kotlin/Int
  annotationClassIds: []
  annotations: []
  callableIdIfNonLocal: java/lang/String.lastIndexOfSupplementary
  dispatchType: java/lang/String
  hasStableParameterNames: false
  isExtension: false
  isExternal: false
  isInfix: false
  isInline: false
  isOperator: false
  isOverride: false
  isStatic: false
  isSuspend: false
  modality: OPEN
  name: lastIndexOfSupplementary
  origin: JAVA
  receiverType: null
  symbolKind: MEMBER
  typeParameters: []
  valueParameters: [
    KtFirValueParameterSymbol(p0)
    KtFirValueParameterSymbol(p1)
  ]
  visibility: Private

KtFirFunctionSymbol:
  annotatedType: [] ft<kotlin/String, kotlin/String?>
  annotationClassIds: []
  annotations: []
  callableIdIfNonLocal: java/lang/String.substring
  dispatchType: java/lang/String
  hasStableParameterNames: false
  isExtension: false
  isExternal: false
  isInfix: false
  isInline: false
  isOperator: false
  isOverride: false
  isStatic: false
  isSuspend: false
  modality: OPEN
  name: substring
  origin: JAVA
  receiverType: null
  symbolKind: MEMBER
  typeParameters: []
  valueParameters: [
    KtFirValueParameterSymbol(p0)
  ]
  visibility: Public

KtFirFunctionSymbol:
  annotatedType: [] ft<kotlin/String, kotlin/String?>
  annotationClassIds: []
  annotations: []
  callableIdIfNonLocal: java/lang/String.substring
  dispatchType: java/lang/String
  hasStableParameterNames: false
  isExtension: false
  isExternal: false
  isInfix: false
  isInline: false
  isOperator: false
  isOverride: false
  isStatic: false
  isSuspend: false
  modality: OPEN
  name: substring
  origin: JAVA
  receiverType: null
  symbolKind: MEMBER
  typeParameters: []
  valueParameters: [
    KtFirValueParameterSymbol(p0)
    KtFirValueParameterSymbol(p1)
  ]
  visibility: Public

KtFirFunctionSymbol:
  annotatedType: [] @EnhancedNullability kotlin/CharSequence
  annotationClassIds: []
  annotations: []
  callableIdIfNonLocal: java/lang/String.subSequence
  dispatchType: java/lang/String
  hasStableParameterNames: false
  isExtension: false
  isExternal: false
  isInfix: false
  isInline: false
  isOperator: false
  isOverride: false
  isStatic: false
  isSuspend: false
  modality: OPEN
  name: subSequence
  origin: JAVA
  receiverType: null
  symbolKind: MEMBER
  typeParameters: []
  valueParameters: [
    KtFirValueParameterSymbol(p0)
    KtFirValueParameterSymbol(p1)
  ]
  visibility: Public

KtFirFunctionSymbol:
  annotatedType: [] ft<kotlin/String, kotlin/String?>
  annotationClassIds: []
  annotations: []
  callableIdIfNonLocal: java/lang/String.concat
  dispatchType: java/lang/String
  hasStableParameterNames: false
  isExtension: false
  isExternal: false
  isInfix: false
  isInline: false
  isOperator: false
  isOverride: false
  isStatic: false
  isSuspend: false
  modality: OPEN
  name: concat
  origin: JAVA
  receiverType: null
  symbolKind: MEMBER
  typeParameters: []
  valueParameters: [
    KtFirValueParameterSymbol(p0)
  ]
  visibility: Public

KtFirFunctionSymbol:
  annotatedType: [] ft<kotlin/String, kotlin/String?>
  annotationClassIds: []
  annotations: []
  callableIdIfNonLocal: java/lang/String.replace
  dispatchType: java/lang/String
  hasStableParameterNames: false
  isExtension: false
  isExternal: false
  isInfix: false
  isInline: false
  isOperator: false
  isOverride: false
  isStatic: false
  isSuspend: false
  modality: OPEN
  name: replace
  origin: JAVA
  receiverType: null
  symbolKind: MEMBER
  typeParameters: []
  valueParameters: [
    KtFirValueParameterSymbol(p0)
    KtFirValueParameterSymbol(p1)
  ]
  visibility: Public

KtFirFunctionSymbol:
  annotatedType: [] ft<kotlin/String, kotlin/String?>
  annotationClassIds: []
  annotations: []
  callableIdIfNonLocal: java/lang/String.replace
  dispatchType: java/lang/String
  hasStableParameterNames: false
  isExtension: false
  isExternal: false
  isInfix: false
  isInline: false
  isOperator: false
  isOverride: false
  isStatic: false
  isSuspend: false
  modality: OPEN
  name: replace
  origin: JAVA
  receiverType: null
  symbolKind: MEMBER
  typeParameters: []
  valueParameters: [
    KtFirValueParameterSymbol(p0)
    KtFirValueParameterSymbol(p1)
  ]
  visibility: Public

KtFirFunctionSymbol:
  annotatedType: [] kotlin/Boolean
  annotationClassIds: []
  annotations: []
  callableIdIfNonLocal: java/lang/String.matches
  dispatchType: java/lang/String
  hasStableParameterNames: false
  isExtension: false
  isExternal: false
  isInfix: false
  isInline: false
  isOperator: false
  isOverride: false
  isStatic: false
  isSuspend: false
  modality: OPEN
  name: matches
  origin: JAVA
  receiverType: null
  symbolKind: MEMBER
  typeParameters: []
  valueParameters: [
    KtFirValueParameterSymbol(p0)
  ]
  visibility: Public

KtFirFunctionSymbol:
  annotatedType: [] kotlin/Boolean
  annotationClassIds: []
  annotations: []
  callableIdIfNonLocal: java/lang/String.contains
  dispatchType: java/lang/String
  hasStableParameterNames: false
  isExtension: false
  isExternal: false
  isInfix: false
  isInline: false
  isOperator: true
  isOverride: false
  isStatic: false
  isSuspend: false
  modality: OPEN
  name: contains
  origin: JAVA
  receiverType: null
  symbolKind: MEMBER
  typeParameters: []
  valueParameters: [
    KtFirValueParameterSymbol(p0)
  ]
  visibility: Public

KtFirFunctionSymbol:
  annotatedType: [] ft<kotlin/String, kotlin/String?>
  annotationClassIds: []
  annotations: []
  callableIdIfNonLocal: java/lang/String.replaceFirst
  dispatchType: java/lang/String
  hasStableParameterNames: false
  isExtension: false
  isExternal: false
  isInfix: false
  isInline: false
  isOperator: false
  isOverride: false
  isStatic: false
  isSuspend: false
  modality: OPEN
  name: replaceFirst
  origin: JAVA
  receiverType: null
  symbolKind: MEMBER
  typeParameters: []
  valueParameters: [
    KtFirValueParameterSymbol(p0)
    KtFirValueParameterSymbol(p1)
  ]
  visibility: Public

KtFirFunctionSymbol:
  annotatedType: [] ft<kotlin/String, kotlin/String?>
  annotationClassIds: []
  annotations: []
  callableIdIfNonLocal: java/lang/String.replaceAll
  dispatchType: java/lang/String
  hasStableParameterNames: false
  isExtension: false
  isExternal: false
  isInfix: false
  isInline: false
  isOperator: false
  isOverride: false
  isStatic: false
  isSuspend: false
  modality: OPEN
  name: replaceAll
  origin: JAVA
  receiverType: null
  symbolKind: MEMBER
  typeParameters: []
  valueParameters: [
    KtFirValueParameterSymbol(p0)
    KtFirValueParameterSymbol(p1)
  ]
  visibility: Public

KtFirFunctionSymbol:
  annotatedType: [] ft<kotlin/Array<ft<kotlin/String, kotlin/String?>>, kotlin/Array<out ft<kotlin/String, kotlin/String?>>?>
  annotationClassIds: []
  annotations: []
  callableIdIfNonLocal: java/lang/String.split
  dispatchType: java/lang/String
  hasStableParameterNames: false
  isExtension: false
  isExternal: false
  isInfix: false
  isInline: false
  isOperator: false
  isOverride: false
  isStatic: false
  isSuspend: false
  modality: OPEN
  name: split
  origin: JAVA
  receiverType: null
  symbolKind: MEMBER
  typeParameters: []
  valueParameters: [
    KtFirValueParameterSymbol(p0)
    KtFirValueParameterSymbol(p1)
  ]
  visibility: Public

KtFirFunctionSymbol:
  annotatedType: [] ft<kotlin/Array<ft<kotlin/String, kotlin/String?>>, kotlin/Array<out ft<kotlin/String, kotlin/String?>>?>
  annotationClassIds: []
  annotations: []
  callableIdIfNonLocal: java/lang/String.split
  dispatchType: java/lang/String
  hasStableParameterNames: false
  isExtension: false
  isExternal: false
  isInfix: false
  isInline: false
  isOperator: false
  isOverride: false
  isStatic: false
  isSuspend: false
  modality: OPEN
  name: split
  origin: JAVA
  receiverType: null
  symbolKind: MEMBER
  typeParameters: []
  valueParameters: [
    KtFirValueParameterSymbol(p0)
  ]
  visibility: Public

KtFirFunctionSymbol:
  annotatedType: [] ft<kotlin/String, kotlin/String?>
  annotationClassIds: []
  annotations: []
  callableIdIfNonLocal: java/lang/String.toLowerCase
  dispatchType: java/lang/String
  hasStableParameterNames: false
  isExtension: false
  isExternal: false
  isInfix: false
  isInline: false
  isOperator: false
  isOverride: false
  isStatic: false
  isSuspend: false
  modality: OPEN
  name: toLowerCase
  origin: JAVA
  receiverType: null
  symbolKind: MEMBER
  typeParameters: []
  valueParameters: [
    KtFirValueParameterSymbol(p0)
  ]
  visibility: Public

KtFirFunctionSymbol:
  annotatedType: [] ft<kotlin/String, kotlin/String?>
  annotationClassIds: []
  annotations: []
  callableIdIfNonLocal: java/lang/String.toLowerCase
  dispatchType: java/lang/String
  hasStableParameterNames: false
  isExtension: false
  isExternal: false
  isInfix: false
  isInline: false
  isOperator: false
  isOverride: false
  isStatic: false
  isSuspend: false
  modality: OPEN
  name: toLowerCase
  origin: JAVA
  receiverType: null
  symbolKind: MEMBER
  typeParameters: []
  valueParameters: []
  visibility: Public

KtFirFunctionSymbol:
  annotatedType: [] ft<kotlin/String, kotlin/String?>
  annotationClassIds: []
  annotations: []
  callableIdIfNonLocal: java/lang/String.toUpperCase
  dispatchType: java/lang/String
  hasStableParameterNames: false
  isExtension: false
  isExternal: false
  isInfix: false
  isInline: false
  isOperator: false
  isOverride: false
  isStatic: false
  isSuspend: false
  modality: OPEN
  name: toUpperCase
  origin: JAVA
  receiverType: null
  symbolKind: MEMBER
  typeParameters: []
  valueParameters: [
    KtFirValueParameterSymbol(p0)
  ]
  visibility: Public

KtFirFunctionSymbol:
  annotatedType: [] ft<kotlin/String, kotlin/String?>
  annotationClassIds: []
  annotations: []
  callableIdIfNonLocal: java/lang/String.toUpperCase
  dispatchType: java/lang/String
  hasStableParameterNames: false
  isExtension: false
  isExternal: false
  isInfix: false
  isInline: false
  isOperator: false
  isOverride: false
  isStatic: false
  isSuspend: false
  modality: OPEN
  name: toUpperCase
  origin: JAVA
  receiverType: null
  symbolKind: MEMBER
  typeParameters: []
  valueParameters: []
  visibility: Public

KtFirFunctionSymbol:
  annotatedType: [] ft<kotlin/String, kotlin/String?>
  annotationClassIds: []
  annotations: []
  callableIdIfNonLocal: java/lang/String.trim
  dispatchType: java/lang/String
  hasStableParameterNames: false
  isExtension: false
  isExternal: false
  isInfix: false
  isInline: false
  isOperator: false
  isOverride: false
  isStatic: false
  isSuspend: false
  modality: OPEN
  name: trim
  origin: JAVA
  receiverType: null
  symbolKind: MEMBER
  typeParameters: []
  valueParameters: []
  visibility: Public

KtFirFunctionSymbol:
  annotatedType: [] @EnhancedNullability kotlin/String
  annotationClassIds: []
  annotations: []
  callableIdIfNonLocal: java/lang/String.toString
  dispatchType: java/lang/String
  hasStableParameterNames: false
  isExtension: false
  isExternal: false
  isInfix: false
  isInline: false
  isOperator: false
  isOverride: false
  isStatic: false
  isSuspend: false
  modality: OPEN
  name: toString
  origin: JAVA
  receiverType: null
  symbolKind: MEMBER
  typeParameters: []
  valueParameters: []
  visibility: Public

KtFirFunctionSymbol:
  annotatedType: [] ft<kotlin/CharArray, kotlin/CharArray?>
  annotationClassIds: []
  annotations: []
  callableIdIfNonLocal: java/lang/String.toCharArray
  dispatchType: java/lang/String
  hasStableParameterNames: false
  isExtension: false
  isExternal: false
  isInfix: false
  isInline: false
  isOperator: false
  isOverride: false
  isStatic: false
  isSuspend: false
  modality: OPEN
  name: toCharArray
  origin: JAVA
  receiverType: null
  symbolKind: MEMBER
  typeParameters: []
  valueParameters: []
  visibility: Public

KtFirFunctionSymbol:
  annotatedType: [] ft<kotlin/String, kotlin/String?>
  annotationClassIds: []
  annotations: []
  callableIdIfNonLocal: java/lang/String.intern
  dispatchType: java/lang/String
  hasStableParameterNames: false
  isExtension: false
  isExternal: false
  isInfix: false
  isInline: false
  isOperator: false
  isOverride: false
  isStatic: false
  isSuspend: false
  modality: OPEN
  name: intern
  origin: JAVA
  receiverType: null
  symbolKind: MEMBER
  typeParameters: []
  valueParameters: []
  visibility: Public

KtFirFunctionSymbol:
  annotatedType: [] kotlin/Char
  annotationClassIds: []
  annotations: []
  callableIdIfNonLocal: kotlin/CharSequence.get
  dispatchType: @EnhancedNullability kotlin/CharSequence
  hasStableParameterNames: true
  isExtension: false
  isExternal: false
  isInfix: false
  isInline: false
  isOperator: true
  isOverride: false
  isStatic: false
  isSuspend: false
  modality: ABSTRACT
  name: get
  origin: LIBRARY
  receiverType: null
  symbolKind: MEMBER
  typeParameters: []
  valueParameters: [
    KtFirValueParameterSymbol(index)
  ]
  visibility: Public

KtFirNamedClassOrObjectSymbol:
  annotationClassIds: []
  annotations: []
  classIdIfNonLocal: java/lang/String.CaseInsensitiveComparator
  classKind: CLASS
  companionObject: null
  isData: false
  isExternal: false
  isFun: false
  isInline: false
  isInner: false
  modality: OPEN
  name: CaseInsensitiveComparator
  origin: JAVA
  superTypes: [
    [] kotlin/Any
    [] java/util/Comparator<ft<kotlin/String, kotlin/String?>>
    [] java/io/Serializable
  ]
  symbolKind: MEMBER
  typeParameters: []
  visibility: Private

KtFirConstructorSymbol:
  annotatedType: [] java/lang/String
  annotationClassIds: []
  annotations: []
  callableIdIfNonLocal: null
  containingClassIdIfNonLocal: java/lang/String
  dispatchType: null
  hasStableParameterNames: false
  isExtension: false
  isPrimary: false
  origin: JAVA
  receiverType: null
  symbolKind: MEMBER
  typeParameters: []
  valueParameters: []
  visibility: Public

KtFirConstructorSymbol:
  annotatedType: [] java/lang/String
  annotationClassIds: []
  annotations: []
  callableIdIfNonLocal: null
  containingClassIdIfNonLocal: java/lang/String
  dispatchType: null
  hasStableParameterNames: false
  isExtension: false
  isPrimary: false
  origin: JAVA
  receiverType: null
  symbolKind: MEMBER
  typeParameters: []
  valueParameters: [
    KtFirValueParameterSymbol(p0)
  ]
  visibility: Public

KtFirConstructorSymbol:
  annotatedType: [] java/lang/String
  annotationClassIds: []
  annotations: []
  callableIdIfNonLocal: null
  containingClassIdIfNonLocal: java/lang/String
  dispatchType: null
  hasStableParameterNames: false
  isExtension: false
  isPrimary: false
  origin: JAVA
  receiverType: null
  symbolKind: MEMBER
  typeParameters: []
  valueParameters: [
    KtFirValueParameterSymbol(p0)
  ]
  visibility: Public

KtFirConstructorSymbol:
  annotatedType: [] java/lang/String
  annotationClassIds: []
  annotations: []
  callableIdIfNonLocal: null
  containingClassIdIfNonLocal: java/lang/String
  dispatchType: null
  hasStableParameterNames: false
  isExtension: false
  isPrimary: false
  origin: JAVA
  receiverType: null
  symbolKind: MEMBER
  typeParameters: []
  valueParameters: [
    KtFirValueParameterSymbol(p0)
    KtFirValueParameterSymbol(p1)
    KtFirValueParameterSymbol(p2)
  ]
  visibility: Public

KtFirConstructorSymbol:
  annotatedType: [] java/lang/String
  annotationClassIds: []
  annotations: []
  callableIdIfNonLocal: null
  containingClassIdIfNonLocal: java/lang/String
  dispatchType: null
  hasStableParameterNames: false
  isExtension: false
  isPrimary: false
  origin: JAVA
  receiverType: null
  symbolKind: MEMBER
  typeParameters: []
  valueParameters: [
    KtFirValueParameterSymbol(p0)
    KtFirValueParameterSymbol(p1)
    KtFirValueParameterSymbol(p2)
  ]
  visibility: Public

KtFirConstructorSymbol:
  annotatedType: [] java/lang/String
  annotationClassIds: [
    kotlin/Deprecated
  ]
  annotations: [
    kotlin/Deprecated(message = Deprecated in Java)
      psi: null
  ]
  callableIdIfNonLocal: null
  containingClassIdIfNonLocal: java/lang/String
  dispatchType: null
  hasStableParameterNames: false
  isExtension: false
  isPrimary: false
  origin: JAVA
  receiverType: null
  symbolKind: MEMBER
  typeParameters: []
  valueParameters: [
    KtFirValueParameterSymbol(p0)
    KtFirValueParameterSymbol(p1)
    KtFirValueParameterSymbol(p2)
    KtFirValueParameterSymbol(p3)
  ]
  visibility: Public

KtFirConstructorSymbol:
  annotatedType: [] java/lang/String
  annotationClassIds: [
    kotlin/Deprecated
  ]
  annotations: [
    kotlin/Deprecated(message = Deprecated in Java)
      psi: null
  ]
  callableIdIfNonLocal: null
  containingClassIdIfNonLocal: java/lang/String
  dispatchType: null
  hasStableParameterNames: false
  isExtension: false
  isPrimary: false
  origin: JAVA
  receiverType: null
  symbolKind: MEMBER
  typeParameters: []
  valueParameters: [
    KtFirValueParameterSymbol(p0)
    KtFirValueParameterSymbol(p1)
  ]
  visibility: Public

KtFirConstructorSymbol:
  annotatedType: [] java/lang/String
  annotationClassIds: []
  annotations: []
  callableIdIfNonLocal: null
  containingClassIdIfNonLocal: java/lang/String
  dispatchType: null
  hasStableParameterNames: false
  isExtension: false
  isPrimary: false
  origin: JAVA
  receiverType: null
  symbolKind: MEMBER
  typeParameters: []
  valueParameters: [
    KtFirValueParameterSymbol(p0)
    KtFirValueParameterSymbol(p1)
    KtFirValueParameterSymbol(p2)
    KtFirValueParameterSymbol(p3)
  ]
  visibility: Public

KtFirConstructorSymbol:
  annotatedType: [] java/lang/String
  annotationClassIds: []
  annotations: []
  callableIdIfNonLocal: null
  containingClassIdIfNonLocal: java/lang/String
  dispatchType: null
  hasStableParameterNames: false
  isExtension: false
  isPrimary: false
  origin: JAVA
  receiverType: null
  symbolKind: MEMBER
  typeParameters: []
  valueParameters: [
    KtFirValueParameterSymbol(p0)
    KtFirValueParameterSymbol(p1)
    KtFirValueParameterSymbol(p2)
    KtFirValueParameterSymbol(p3)
  ]
  visibility: Public

KtFirConstructorSymbol:
  annotatedType: [] java/lang/String
  annotationClassIds: []
  annotations: []
  callableIdIfNonLocal: null
  containingClassIdIfNonLocal: java/lang/String
  dispatchType: null
  hasStableParameterNames: false
  isExtension: false
  isPrimary: false
  origin: JAVA
  receiverType: null
  symbolKind: MEMBER
  typeParameters: []
  valueParameters: [
    KtFirValueParameterSymbol(p0)
    KtFirValueParameterSymbol(p1)
  ]
  visibility: Public

KtFirConstructorSymbol:
  annotatedType: [] java/lang/String
  annotationClassIds: []
  annotations: []
  callableIdIfNonLocal: null
  containingClassIdIfNonLocal: java/lang/String
  dispatchType: null
  hasStableParameterNames: false
  isExtension: false
  isPrimary: false
  origin: JAVA
  receiverType: null
  symbolKind: MEMBER
  typeParameters: []
  valueParameters: [
    KtFirValueParameterSymbol(p0)
    KtFirValueParameterSymbol(p1)
  ]
  visibility: Public

KtFirConstructorSymbol:
  annotatedType: [] java/lang/String
  annotationClassIds: []
  annotations: []
  callableIdIfNonLocal: null
  containingClassIdIfNonLocal: java/lang/String
  dispatchType: null
  hasStableParameterNames: false
  isExtension: false
  isPrimary: false
  origin: JAVA
  receiverType: null
  symbolKind: MEMBER
  typeParameters: []
  valueParameters: [
    KtFirValueParameterSymbol(p0)
    KtFirValueParameterSymbol(p1)
    KtFirValueParameterSymbol(p2)
  ]
  visibility: Public

KtFirConstructorSymbol:
  annotatedType: [] java/lang/String
  annotationClassIds: []
  annotations: []
  callableIdIfNonLocal: null
  containingClassIdIfNonLocal: java/lang/String
  dispatchType: null
  hasStableParameterNames: false
  isExtension: false
  isPrimary: false
  origin: JAVA
  receiverType: null
  symbolKind: MEMBER
  typeParameters: []
  valueParameters: [
    KtFirValueParameterSymbol(p0)
  ]
  visibility: Public

KtFirConstructorSymbol:
  annotatedType: [] java/lang/String
  annotationClassIds: []
  annotations: []
  callableIdIfNonLocal: null
  containingClassIdIfNonLocal: java/lang/String
  dispatchType: null
  hasStableParameterNames: false
  isExtension: false
  isPrimary: false
  origin: JAVA
  receiverType: null
  symbolKind: MEMBER
  typeParameters: []
  valueParameters: [
    KtFirValueParameterSymbol(p0)
  ]
  visibility: Public

KtFirConstructorSymbol:
  annotatedType: [] java/lang/String
  annotationClassIds: []
  annotations: []
  callableIdIfNonLocal: null
  containingClassIdIfNonLocal: java/lang/String
  dispatchType: null
  hasStableParameterNames: false
  isExtension: false
  isPrimary: false
  origin: JAVA
  receiverType: null
  symbolKind: MEMBER
  typeParameters: []
  valueParameters: [
    KtFirValueParameterSymbol(p0)
  ]
  visibility: Public

KtFirConstructorSymbol:
  annotatedType: [] java/lang/String
  annotationClassIds: []
  annotations: []
  callableIdIfNonLocal: null
  containingClassIdIfNonLocal: java/lang/String
  dispatchType: null
  hasStableParameterNames: false
  isExtension: false
  isPrimary: false
  origin: JAVA
  receiverType: null
  symbolKind: MEMBER
  typeParameters: []
  valueParameters: [
    KtFirValueParameterSymbol(p0)
    KtFirValueParameterSymbol(p1)
  ]
  visibility: PackageVisibility

KtFirConstructorSymbol:
  annotatedType: [] java/lang/String
  annotationClassIds: [
    kotlin/Deprecated
  ]
  annotations: [
    kotlin/Deprecated(message = Deprecated in Java)
      psi: null
  ]
  callableIdIfNonLocal: null
  containingClassIdIfNonLocal: java/lang/String
  dispatchType: null
  hasStableParameterNames: false
  isExtension: false
  isPrimary: false
  origin: JAVA
  receiverType: null
  symbolKind: MEMBER
  typeParameters: []
  valueParameters: [
    KtFirValueParameterSymbol(p0)
    KtFirValueParameterSymbol(p1)
    KtFirValueParameterSymbol(p2)
  ]
  visibility: PackageVisibility
*/
