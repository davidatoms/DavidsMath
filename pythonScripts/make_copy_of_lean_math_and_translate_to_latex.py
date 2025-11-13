#!/usr/bin/env python3
"""
Convert Lean 4 files to Markdown with LaTeX formatting.
Reads all .lean files in the DavidsMath directory and creates corresponding .md files.
"""

import os
import re
from pathlib import Path


def lean_to_latex(lean_code):
    """
    Convert Lean mathematical expressions to LaTeX format.
    This is a simplified conversion - complex expressions may need manual adjustment.
    """
    # Handle common Lean syntax patterns
    latex = lean_code

    # Replace Lean operators with LaTeX equivalents
    replacements = {
        r'→': r'\to',
        r'∀': r'\forall',
        r'∃': r'\exists',
        r'λ': r'\lambda',
        r'≤': r'\leq',
        r'≥': r'\geq',
        r'≠': r'\neq',
        r'∈': r'\in',
        r'∉': r'\notin',
        r'⊆': r'\subseteq',
        r'⊂': r'\subset',
        r'∪': r'\cup',
        r'∩': r'\cap',
        r'×': r'\times',
        r'·': r'\cdot',
        r'ℝ': r'\mathbb{R}',
        r'ℕ': r'\mathbb{N}',
        r'ℤ': r'\mathbb{Z}',
        r'ℚ': r'\mathbb{Q}',
        r'ℂ': r'\mathbb{C}',
    }

    for lean_sym, latex_sym in replacements.items():
        latex = latex.replace(lean_sym, latex_sym)

    return latex


def convert_lean_to_markdown(lean_content, filename):
    """
    Convert Lean file content to Markdown with LaTeX.
    """
    lines = lean_content.split('\n')
    markdown_lines = []

    # Add title based on filename
    title = filename.replace('.lean', '').replace('_', ' ')
    markdown_lines.append(f"# {title}\n")

    in_comment_block = False
    in_code_block = False
    current_definition = []

    for line in lines:
        stripped = line.strip()

        # Handle single-line comments
        if stripped.startswith('--'):
            comment_text = stripped[2:].strip()
            if comment_text:
                markdown_lines.append(f"{comment_text}\n")
            else:
                markdown_lines.append("\n")

        # Handle multi-line comments
        elif '/-' in stripped:
            in_comment_block = True
            comment_text = stripped.split('/-', 1)[1]
            if '-/' in comment_text:
                comment_text = comment_text.split('-/', 1)[0]
                in_comment_block = False
            markdown_lines.append(f"{comment_text.strip()}\n")

        elif in_comment_block:
            if '-/' in stripped:
                in_comment_block = False
                comment_text = stripped.split('-/', 1)[0]
                markdown_lines.append(f"{comment_text.strip()}\n")
            else:
                markdown_lines.append(f"{stripped}\n")

        # Handle Lean code (definitions, theorems, etc.)
        elif any(keyword in stripped for keyword in ['def ', 'theorem ', 'lemma ', 'structure ', 'class ', 'axiom ', 'instance ']):
            # Start collecting definition
            current_definition = [line]
            in_code_block = True

        elif in_code_block:
            current_definition.append(line)
            # Check if definition is complete (simplified heuristic)
            if stripped and not stripped.startswith(' ') and not stripped.startswith('\t'):
                if ':=' in stripped or stripped.startswith('end'):
                    # Output the collected definition as LaTeX
                    definition_text = '\n'.join(current_definition)
                    latex_text = lean_to_latex(definition_text)
                    markdown_lines.append(f"$$\n{latex_text}\n$$\n")
                    current_definition = []
                    in_code_block = False

        # Handle imports and namespace declarations
        elif stripped.startswith('import ') or stripped.startswith('open ') or stripped.startswith('namespace '):
            markdown_lines.append(f"```lean\n{stripped}\n```\n")

        # Handle other non-empty lines as potential mathematical content
        elif stripped:
            # Check if it looks like a mathematical expression
            if any(sym in stripped for sym in [':', '→', '∀', '∃', '=', '≤', '≥', '∈']):
                latex_text = lean_to_latex(stripped)
                markdown_lines.append(f"$${latex_text}$$\n")
            else:
                markdown_lines.append(f"{stripped}\n")

        else:
            # Empty line
            markdown_lines.append("\n")

    # Handle any remaining definition
    if current_definition:
        definition_text = '\n'.join(current_definition)
        latex_text = lean_to_latex(definition_text)
        markdown_lines.append(f"$$\n{latex_text}\n$$\n")

    return ''.join(markdown_lines)


def process_lean_files(directory):
    """
    Process all .lean files in the given directory.
    """
    directory_path = Path(directory)
    lean_files = list(directory_path.glob('*.lean'))

    print(f"Found {len(lean_files)} .lean files to convert")

    converted_count = 0

    for lean_file in lean_files:
        try:
            # Read the .lean file
            with open(lean_file, 'r', encoding='utf-8') as f:
                lean_content = f.read()

            # Convert to markdown
            markdown_content = convert_lean_to_markdown(lean_content, lean_file.name)

            # Write to .md file
            md_file = lean_file.with_suffix('.md')
            with open(md_file, 'w', encoding='utf-8') as f:
                f.write(markdown_content)

            print(f"✓ Converted {lean_file.name} → {md_file.name}")
            converted_count += 1

        except Exception as e:
            print(f"✗ Error converting {lean_file.name}: {e}")

    print(f"\nConversion complete: {converted_count}/{len(lean_files)} files converted successfully")


if __name__ == '__main__':
    # Directory containing the .lean files
    lean_dir = Path(__file__).parent / 'DavidsMath'

    if not lean_dir.exists():
        print(f"Error: Directory {lean_dir} does not exist")
        exit(1)

    process_lean_files(lean_dir)