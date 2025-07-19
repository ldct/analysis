#!/usr/bin/env python3

import os
import re
from pathlib import Path

def extract_section_number(filename):
    """Extract section number from filename like Section_2_1.lean -> (2, 1)"""
    match = re.match(r'Section_(\d+)_(\d+)\.lean', filename)
    if match:
        return (int(match.group(1)), int(match.group(2)))
    
    # Handle epilogue files like Section_2_epilogue.lean -> (2, 999)
    match = re.match(r'Section_(\d+)_epilogue\.lean', filename)
    if match:
        return (int(match.group(1)), 999)
    
    return None

def main():
    # Find all Section_*.lean files in the Analysis directory
    analysis_dir = Path('Analysis')
    section_files = []
    
    for file_path in analysis_dir.glob('Section_*.lean'):
        section_num = extract_section_number(file_path.name)
        if section_num:
            section_files.append((section_num, file_path))
    
    # Sort by section number
    section_files.sort(key=lambda x: x[0])
    
    # Read and print each file's content
    for section_num, file_path in section_files:
        print(f"=== {file_path.name} ===")
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
                print(content)
        except Exception as e:
            print(f"Error reading {file_path}: {e}")
        print()  # Empty line between files

if __name__ == "__main__":
    main()