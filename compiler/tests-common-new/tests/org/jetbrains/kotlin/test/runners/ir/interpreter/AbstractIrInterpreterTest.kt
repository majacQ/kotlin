/*
 * Copyright 2010-2021 JetBrains s.r.o. and Kotlin Programming Language contributors.
 * Use of this source code is governed by the Apache 2.0 license that can be found in the license/LICENSE.txt file.
 */

package org.jetbrains.kotlin.test.runners.ir.interpreter

import org.jetbrains.kotlin.platform.jvm.JvmPlatforms
import org.jetbrains.kotlin.test.TargetBackend
import org.jetbrains.kotlin.test.backend.handlers.IrInterpreterBackendHandler
import org.jetbrains.kotlin.test.backend.ir.JvmIrBackendFacade
import org.jetbrains.kotlin.test.builders.TestConfigurationBuilder
import org.jetbrains.kotlin.test.directives.JvmEnvironmentConfigurationDirectives
import org.jetbrains.kotlin.test.frontend.classic.ClassicFrontend2IrConverter
import org.jetbrains.kotlin.test.frontend.classic.ClassicFrontendFacade
import org.jetbrains.kotlin.test.frontend.fir.Fir2IrResultsConverter
import org.jetbrains.kotlin.test.frontend.fir.FirFrontendFacade
import org.jetbrains.kotlin.test.model.*
import org.jetbrains.kotlin.test.preprocessors.IrInterpreterImplicitKotlinImports
import org.jetbrains.kotlin.test.runners.AbstractKotlinCompilerWithTargetBackendTest
import org.jetbrains.kotlin.test.services.configuration.CommonEnvironmentConfigurator
import org.jetbrains.kotlin.test.services.configuration.JvmEnvironmentConfigurator
import org.jetbrains.kotlin.test.services.sourceProviders.IrInterpreterHelpersSourceFilesProvider

open class AbstractIrInterpreterTest(
    private val frontendKind: FrontendKind<*>
) : AbstractKotlinCompilerWithTargetBackendTest(TargetBackend.JVM_IR) {
    override fun TestConfigurationBuilder.configuration() {
        globalDefaults {
            frontend = frontendKind
            targetPlatform = JvmPlatforms.defaultJvmPlatform
            artifactKind = BinaryKind.NoArtifact
            targetBackend = TargetBackend.JVM_IR
            dependencyKind = DependencyKind.Source
        }

        defaultDirectives {
            +JvmEnvironmentConfigurationDirectives.FULL_JDK
            +JvmEnvironmentConfigurationDirectives.NO_RUNTIME
            +JvmEnvironmentConfigurationDirectives.ALLOW_KOTLIN_PACKAGE
        }

        useConfigurators(
            ::CommonEnvironmentConfigurator,
            ::JvmEnvironmentConfigurator,
        )

        useAdditionalSourceProviders(::IrInterpreterHelpersSourceFilesProvider)
        useSourcePreprocessor(::IrInterpreterImplicitKotlinImports)

        useFrontendFacades(
            ::FirFrontendFacade,
            ::ClassicFrontendFacade,
        )
        useFrontend2BackendConverters(
            ::Fir2IrResultsConverter,
            ::ClassicFrontend2IrConverter,
        )
        useBackendFacades(::JvmIrBackendFacade)

        useBackendHandlers(::IrInterpreterBackendHandler)
        enableMetaInfoHandler()
    }
}

open class AbstractIrInterpreterAfterFir2IrTest : AbstractIrInterpreterTest(FrontendKinds.FIR)
open class AbstractIrInterpreterAfterPsi2IrTest : AbstractIrInterpreterTest(FrontendKinds.ClassicFrontend)
