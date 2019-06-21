// Copyright 2000-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.
package com.intellij.codeInsight.editorActions;

import com.intellij.codeInsight.highlighting.BraceHighlightingHandler;
import com.intellij.codeInsight.highlighting.BraceMatcher;
import com.intellij.codeInsight.highlighting.BraceMatchingUtil;
import com.intellij.codeInsight.highlighting.CodeBlockSupportHandler;
import com.intellij.openapi.actionSystem.CommonDataKeys;
import com.intellij.openapi.actionSystem.DataContext;
import com.intellij.openapi.editor.Caret;
import com.intellij.openapi.editor.Editor;
import com.intellij.openapi.editor.EditorModificationUtil;
import com.intellij.openapi.editor.actionSystem.EditorAction;
import com.intellij.openapi.editor.actionSystem.EditorActionHandler;
import com.intellij.openapi.editor.ex.EditorEx;
import com.intellij.openapi.editor.highlighter.EditorHighlighter;
import com.intellij.openapi.editor.highlighter.HighlighterIterator;
import com.intellij.openapi.fileTypes.FileType;
import com.intellij.openapi.util.TextRange;
import com.intellij.psi.PsiFile;
import com.intellij.psi.util.PsiUtilBase;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

/**
 * Moves caret to the the matching brace:
 * - If caret is on the closing brace - moves in the beginning of the matching opening brace
 * - If caret is on the opening brace - moves to the end of the matching closing brace
 * - Otherwise moves from the caret position to the beginning of the file and finds first opening brace not closed before the caret position
 */
public class MatchBraceAction extends EditorAction {
  public MatchBraceAction() {
    super(new MyHandler());
  }

  private static class MyHandler extends EditorActionHandler {
    MyHandler() {
      super(true);
    }

    @Override
    public void execute(@NotNull Editor editor, DataContext dataContext) {
      final PsiFile file = CommonDataKeys.PSI_FILE.getData(dataContext);
      if (file == null) return;


      int targetOffset = getClosestTargetOffset(editor, file);

      if (targetOffset > -1) {
        moveCaret(editor, editor.getCaretModel().getCurrentCaret(), targetOffset);
      }
    }

    /**
     * Attempts to find closest target offset for the caret. Uses {@link BraceMatcher} and {@link CodeBlockSupportHandler}
     *
     * @return target caret offset or -1 if uncomputable.
     */
    private static int getClosestTargetOffset(@NotNull Editor editor, @NotNull PsiFile file) {
      int offsetFromBraceMatcher = getOffsetFromBraceMatcher(editor, file);
      TextRange rangeFromCodeBlockSupport = CodeBlockSupportHandler.findCodeBlockRange(editor, file);
      if (rangeFromCodeBlockSupport.isEmpty() || rangeFromCodeBlockSupport.contains(offsetFromBraceMatcher)) {
        return offsetFromBraceMatcher;
      }

      final EditorHighlighter highlighter = ((EditorEx)editor).getHighlighter();
      int caretOffset = editor.getCaretModel().getOffset();
      HighlighterIterator iterator = highlighter.createIterator(caretOffset);

      // end of file or at block closing token
      if (iterator.atEnd() || iterator.getEnd() == rangeFromCodeBlockSupport.getEndOffset() ||
          // edge case - end of closing token
          (caretOffset > 0 && highlighter.createIterator(caretOffset - 1).getEnd() == rangeFromCodeBlockSupport.getEndOffset())) {
        return rangeFromCodeBlockSupport.getStartOffset();
      }
      return rangeFromCodeBlockSupport.getEndOffset();
    }

    /**
     * @return offset to move caret to, computed from the brace matcher. If it's not possible to compute - returns {@code -1}
     * @implNote this code partially duplicates {@link BraceHighlightingHandler#updateBraces()} and probably can be extracted.
     */
    private static int getOffsetFromBraceMatcher(@NotNull Editor editor, @NotNull PsiFile file) {
      int offset = editor.getCaretModel().getCurrentCaret().getOffset();
      BraceMatchingContext matchingContext = computeBraceMatchingContext(editor, file, offset);
      if (matchingContext != null) {
        return matchingContext.navigationOffset;
      }
      return tryFindPreviousUnclosedOpeningBraceOffset(editor, file);
    }

    /**
     * Computes context that should be used to highlight and navigate matching braces
     *
     * @param offset offset we are computing for. Some implementations may need to compute this not only for caret position, but for other offsets, e.g. skipping spaces behind or ahead.
     * @return a context should be used or null if there is no matching braces at offset
     * @apiNote this method contains a logic for selecting braces in different complicated situations, like {@code (<caret>(} and so on.
     * It does not looks forward/behind skipping spaces, like highlighting does.
     */
    @Nullable
    private static BraceMatchingContext computeBraceMatchingContext(@NotNull Editor editor,
                                                                    @NotNull PsiFile file,
                                                                    int offset) {
      final EditorHighlighter highlighter = BraceHighlightingHandler.getLazyParsableHighlighterIfAny(file.getProject(), editor, file);
      final CharSequence text = editor.getDocument().getCharsSequence();

      final HighlighterIterator iterator = highlighter.createIterator(offset);
      final FileType fileType = iterator.atEnd() ? null : getFileType(file, iterator.getStart());
      final HighlighterIterator preOffsetIterator = offset > 0 ? highlighter.createIterator(offset - 1) : null;
      final FileType preOffsetFileType = preOffsetIterator != null ? getFileType(file, preOffsetIterator.getStart()) : null;

      boolean isAfterLeftBrace = preOffsetIterator != null &&
                                 BraceMatchingUtil.isLBraceToken(preOffsetIterator, text, preOffsetFileType);
      boolean isAfterRightBrace = !isAfterLeftBrace && preOffsetIterator != null &&
                                  BraceMatchingUtil.isRBraceToken(preOffsetIterator, text, preOffsetFileType);
      boolean isBeforeLeftBrace = fileType != null && BraceMatchingUtil.isLBraceToken(iterator, text, fileType);
      boolean isBeforeRightBrace = !isBeforeLeftBrace && fileType != null && BraceMatchingUtil.isRBraceToken(iterator, text, fileType);

      int offsetTokenStart = iterator.atEnd() ? -1 : iterator.getStart();
      int preOffsetTokenStart = preOffsetIterator == null || preOffsetIterator.atEnd() ? -1 : preOffsetIterator.getStart();

      if (isAfterRightBrace && BraceMatchingUtil.matchBrace(text, preOffsetFileType, preOffsetIterator, false)) {
        return new BraceMatchingContext(preOffsetTokenStart, preOffsetIterator.getStart());
      }
      else if (isBeforeLeftBrace && BraceMatchingUtil.matchBrace(text, fileType, iterator, true)) {
        return new BraceMatchingContext(offsetTokenStart, iterator.getEnd());
      }
      else if (isAfterLeftBrace && BraceMatchingUtil.matchBrace(text, preOffsetFileType, preOffsetIterator, true)) {
        return new BraceMatchingContext(preOffsetTokenStart, preOffsetIterator.getEnd());
      }
      else if (isBeforeRightBrace && BraceMatchingUtil.matchBrace(text, fileType, iterator, false)) {
        return new BraceMatchingContext(offsetTokenStart, iterator.getStart());
      }
      return null;
    }

    /**
     * Describes a brace matching/navigation context computed by {@link #computeBraceMatchingContext
     */
    public static final class BraceMatchingContext {
      public final int currentBraceStartOffset;
      public final int navigationOffset;

      public BraceMatchingContext(int currentBraceStartOffset, int navigationOffset) {
        this.currentBraceStartOffset = currentBraceStartOffset;
        this.navigationOffset = navigationOffset;
      }
    }

    /**
     * Moving back from the caret position closing and opening braces (in dumb way, no need to be same type or whatever). Stops if
     * encounters first opening brace which was not closed before.
     *
     * @return start offset of the opening brace or -1 if non were found.
     */
    private static int tryFindPreviousUnclosedOpeningBraceOffset(@NotNull Editor editor, @NotNull PsiFile file) {
      final EditorHighlighter highlighter = BraceHighlightingHandler.getLazyParsableHighlighterIfAny(file.getProject(), editor, file);
      final CharSequence text = editor.getDocument().getCharsSequence();
      final HighlighterIterator iterator = highlighter.createIterator(editor.getCaretModel().getOffset());
      final FileType fileType = iterator.atEnd() ? null : getFileType(file, iterator.getStart());

      if (fileType == null) {
        return -1;
      }

      int unopenedBraces = 0;
      while (true) {
        if (BraceMatchingUtil.isRBraceToken(iterator, text, fileType)) {
          unopenedBraces++;
        }
        else if (BraceMatchingUtil.isLBraceToken(iterator, text, fileType)) {
          unopenedBraces--;
        }
        if (unopenedBraces < 0) {
          return iterator.getStart();
        }

        if (iterator.getStart() == 0) {
          return -1;
        }
        iterator.retreat();
      }
    }
  }

  @NotNull
  private static FileType getFileType(PsiFile file, int offset) {
    return PsiUtilBase.getPsiFileAtOffset(file, offset).getFileType();
  }

  private static void moveCaret(Editor editor, Caret caret, int offset) {
    caret.removeSelection();
    caret.moveToOffset(offset);
    EditorModificationUtil.scrollToCaret(editor);
  }
}
