/*
 * Copyright 2010-2020 JetBrains s.r.o. and Kotlin Programming Language contributors.
 * Use of this source code is governed by the Apache 2.0 license that can be found in the license/LICENSE.txt file.
 */

package org.jetbrains.kotlin.fir.analysis.checkers.declaration

import org.jetbrains.kotlin.descriptors.ClassKind
import org.jetbrains.kotlin.descriptors.Modality
import org.jetbrains.kotlin.fir.FirSession
import org.jetbrains.kotlin.fir.analysis.checkers.context.CheckerContext
import org.jetbrains.kotlin.fir.analysis.checkers.extractTypeRefAndSourceFromTypeArgument
import org.jetbrains.kotlin.fir.analysis.checkers.toRegularClass
import org.jetbrains.kotlin.fir.analysis.diagnostics.DiagnosticReporter
import org.jetbrains.kotlin.fir.analysis.diagnostics.FirErrors
import org.jetbrains.kotlin.fir.analysis.diagnostics.reportOn
import org.jetbrains.kotlin.fir.analysis.diagnostics.withSuppressedDiagnostics
import org.jetbrains.kotlin.fir.declarations.FirClass
import org.jetbrains.kotlin.fir.declarations.FirRegularClass
import org.jetbrains.kotlin.fir.declarations.FirTypeParameter
import org.jetbrains.kotlin.fir.declarations.modality
import org.jetbrains.kotlin.fir.resolve.fullyExpandedType
import org.jetbrains.kotlin.fir.resolve.substitution.ConeSubstitutorByMap
import org.jetbrains.kotlin.fir.resolve.toSymbol
import org.jetbrains.kotlin.fir.symbols.impl.FirRegularClassSymbol
import org.jetbrains.kotlin.fir.symbols.impl.FirTypeParameterSymbol
import org.jetbrains.kotlin.fir.typeContext
import org.jetbrains.kotlin.fir.types.*
import org.jetbrains.kotlin.types.AbstractTypeChecker
import org.jetbrains.kotlin.utils.addToStdlib.safeAs

object FirSupertypesChecker : FirClassChecker() {
    override fun check(declaration: FirClass<*>, context: CheckerContext, reporter: DiagnosticReporter) {
        val isInterface = declaration.classKind == ClassKind.INTERFACE
        var nullableSupertypeReported = false
        var extensionFunctionSupertypeReported = false
        var interfaceWithSuperclassReported = !isInterface
        var finalSupertypeReported = false
        var singletonInSupertypeReported = false
        var classAppeared = false
        val superClassSymbols = hashSetOf<FirRegularClassSymbol>()
        for (superTypeRef in declaration.superTypeRefs) {
            withSuppressedDiagnostics(superTypeRef, context) {
                val coneType = superTypeRef.coneType
                if (!nullableSupertypeReported && coneType.nullability == ConeNullability.NULLABLE) {
                    reporter.reportOn(superTypeRef.source, FirErrors.NULLABLE_SUPERTYPE, context)
                    nullableSupertypeReported = true
                }
                if (!extensionFunctionSupertypeReported && coneType.isExtensionFunctionType) {
                    reporter.reportOn(superTypeRef.source, FirErrors.SUPERTYPE_IS_EXTENSION_FUNCTION_TYPE, context)
                    extensionFunctionSupertypeReported = true
                }
                val lookupTag = coneType.safeAs<ConeClassLikeType>()?.lookupTag ?: return@withSuppressedDiagnostics
                val superTypeFir = lookupTag.toSymbol(context.session)?.fir

                if (superTypeFir is FirRegularClass) {
                    if (!superClassSymbols.add(superTypeFir.symbol)) {
                        reporter.reportOn(superTypeRef.source, FirErrors.SUPERTYPE_APPEARS_TWICE, context)
                    }
                    if (superTypeFir.classKind != ClassKind.INTERFACE) {
                        if (classAppeared) {
                            reporter.reportOn(superTypeRef.source, FirErrors.MANY_CLASSES_IN_SUPERTYPE_LIST, context)
                        } else {
                            classAppeared = true
                        }
                        if (!interfaceWithSuperclassReported) {
                            reporter.reportOn(superTypeRef.source, FirErrors.INTERFACE_WITH_SUPERCLASS, context)
                            interfaceWithSuperclassReported = true
                        }
                    }
                    val isObject = superTypeFir.classKind == ClassKind.OBJECT
                    if (!finalSupertypeReported && !isObject && superTypeFir.modality == Modality.FINAL) {
                        reporter.reportOn(superTypeRef.source, FirErrors.FINAL_SUPERTYPE, context)
                        finalSupertypeReported = true
                    }
                    if (!singletonInSupertypeReported && isObject) {
                        reporter.reportOn(superTypeRef.source, FirErrors.SINGLETON_IN_SUPERTYPE, context)
                        singletonInSupertypeReported = true
                    }
                }

                for (annotation in superTypeRef.annotations) {
                    withSuppressedDiagnostics(annotation, context) {
                        if (annotation.useSiteTarget != null) {
                            reporter.reportOn(annotation.source, FirErrors.ANNOTATION_ON_SUPERCLASS, context)
                        }
                    }
                }
            }

            val coneType = superTypeRef.coneType
            if (coneType.typeArguments.isNotEmpty()) {
                for ((index, typeArgument) in coneType.typeArguments.withIndex()) {
                    if (typeArgument.isConflictingOrNotInvariant) {
                        val (_, argSource) = extractTypeRefAndSourceFromTypeArgument(superTypeRef, index) ?: continue
                        reporter.reportOn(
                            argSource ?: superTypeRef.source,
                            FirErrors.PROJECTION_IN_IMMEDIATE_ARGUMENT_TO_SUPERTYPE,
                            context
                        )
                    }
                }
            } else {
                val fullyExpandedType = coneType.fullyExpandedType(context.session)
                if (isInterface(fullyExpandedType, context.session)) {
                    for (typeArgument in fullyExpandedType.typeArguments) {
                        if (typeArgument.isConflictingOrNotInvariant) {
                            reporter.reportOn(superTypeRef.source, FirErrors.EXPANDED_TYPE_CANNOT_BE_INHERITED, coneType, context)
                            break
                        }
                    }
                }
            }
        }

        val declSource = declaration.source
        if (declaration is FirRegularClass && declaration.superTypeRefs.size > 1 && declSource != null) {
            val result = buildDeepSubstitutionMultimap(declaration, context.session)
            for ((typeParameterSymbol, typeAndProjections) in result) {
                val projections = typeAndProjections.projections
                if (projections.size > 1) {
                    reporter.report(
                        FirErrors.INCONSISTENT_TYPE_PARAMETER_VALUES.on(
                            declSource, typeParameterSymbol, typeAndProjections.classSymbol, projections
                        ), context
                    )
                }
            }
        }
    }

    private fun isInterface(type: ConeKotlinType, session: FirSession): Boolean {
        val symbol = type.toSymbol(session)
        return symbol is FirRegularClassSymbol && symbol.fir.classKind == ClassKind.INTERFACE
    }

    private fun buildDeepSubstitutionMultimap(
        firClass: FirRegularClass,
        session: FirSession
    ): Map<FirTypeParameterSymbol, ClassSymbolAndProjections> {
        val result = mutableMapOf<FirTypeParameterSymbol, ClassSymbolAndProjections>()
        val substitution = mutableMapOf<FirTypeParameterSymbol, ConeKotlinType>()
        val substitutor = ConeSubstitutorByMap(substitution, session)
        val typeContext = session.typeContext

        fun fillInDeepSubstitutor(firTypeRef: FirTypeRef?, firClass: FirRegularClass) {
            if (firTypeRef?.isEnum == true) {
                return
            }

            if (firTypeRef is FirResolvedTypeRef) {
                val typeArguments = firTypeRef.type.typeArguments
                val typeParameters = firClass.typeParameters
                val count = minOf(typeArguments.size, typeParameters.size)
                for (index in 0 until count) {
                    val typeArgument = typeArguments[index]
                    val typeParameterSymbol = typeParameters[index].symbol

                    val substitute = substitutor.substituteArgument(typeArgument) ?: typeArgument
                    val substituteType = (substitute as? ConeKotlinTypeProjection)?.type ?: continue

                    substitution[typeParameterSymbol] = substituteType
                    var classSymbolAndProjections = result[typeParameterSymbol]
                    val projections: MutableList<ConeKotlinType>

                    if (classSymbolAndProjections == null) {
                        projections = mutableListOf()
                        classSymbolAndProjections = ClassSymbolAndProjections(firClass.symbol, projections)
                        result[typeParameterSymbol] = classSymbolAndProjections
                    } else {
                        projections = classSymbolAndProjections.projections
                    }

                    if (projections.all {
                            it != substitute && !AbstractTypeChecker.equalTypes(typeContext, it, substituteType)
                        }) {
                        projections.add(substituteType)
                    }
                }
            }

            for (superTypeRef in firClass.superTypeRefs) {
                val superTypeClass = superTypeRef.toRegularClass(session)
                if (superTypeClass != null) {
                    fillInDeepSubstitutor(superTypeRef, superTypeClass)
                }
            }
        }

        fillInDeepSubstitutor(null, firClass)
        return result
    }

    private data class ClassSymbolAndProjections(val classSymbol: FirRegularClassSymbol, val projections: MutableList<ConeKotlinType>)
}
