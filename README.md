# DICOM SNR Analyzer (GetSNR)

This repository contains the source code for the DICOM SNR Analyzer. Follow the steps below to compile the script into a standalone, native macOS application bundle (`.app`).

## Build Prerequisites
Before building, ensure you have **Python 3** installed on your Mac. You can check this by running `python3 --version` in your Terminal.

---

## Disclaimer
This project was developed with the assistance of AI tools. Although the program has been tested thoroughly, bugs may still appear. The software is provided **"as is"** without any guarantees of correctness. Please review the code before running it in a production environment. 


## How to Build the macOS App

### Step 1: Open Terminal and Navigate to the Project Folder
Open your **Terminal** app and use the `cd` command to navigate to the directory where your source files are stored:
```bash
cd path/to/your/GetSNR
```
*(Optional) Verify you are in the correct folder by listing the files:*
```bash
ls
```

### Step 2: Clean Up Old Builds (If applicable)
If you have compiled this application before, wipe the previous build data to ensure a clean slate:
```bash
rm -rf build dist GetSNR.spec
```

### Step 3: Set Up the Virtual Environment
Using a virtual environment keeps the final app size small by excluding global Python packages.

1. **Create the environment** (Skip this if the `snr_env` folder already exists):
   ```bash
   python3 -m venv snr_env
   ```
2. **Activate the environment**:
   ```bash
   source snr_env/bin/activate
   ```
   *(Your terminal prompt will now show `(snr_env)`).*

### Step 4: Install Dependencies
Install the required external libraries. Note that standard Python libraries (like `sys`, `os`, `math`, etc.) are built-in and do not need to be installed.

```bash
# Upgrade pip first
pip install --upgrade pip

# Install external packages using the requirements.txt:
pip install -r requirements.txt
```
If the install is preferred without using requirements.txt, use the following, otherwise go directly to Step 5:

```bash
# Install external packages (Pillow is the pip package for PIL)
pip install pydicom numpy Pillow

# Install PyInstaller
pip install pyinstaller
```

### Step 5: Package the Application
Run the following unified PyInstaller command to compile the script into a standalone app bundle, while explicitly excluding heavy, unused frameworks:

```bash
pyinstaller --name "GetSNR" \
    --windowed \
    --icon=GetSNR2.icns \
    --exclude-module matplotlib \
    --exclude-module scipy \
    --exclude-module pandas \
    dicom_snr_analyzer.py
```

### Step 6: Install & Clean Up
1. Your finished application is now located inside the newly created **`dist/`** folder. 
2. Drag **`GetSNR.app`** from the `dist/` folder into your macOS **Applications** folder.
3. You can now launch it via Launchpad or drag it into your Dock for easy access.
4. Finally, safely deactivate your virtual environment in the Terminal:
   ```bash
   deactivate
   ```

Installation complete! Enjoy the program.

## Assets
- `GetSNR2.icns`: The official application icon used for macOS packaging.

## License
This project is licensed under the MIT License - see the [LICENSE](LICENSE) file for details.

## Reporting Bugs & Feedback

If you encounter any bugs, glitches, or unexpected behavior, please do not send an email. 

Instead, navigate to the **Issues** tab at the top of this GitHub repository page and click **"New issue"**. 

When submitting a bug report, please include:
- A brief description of the bug.
- Steps to reproduce the issue.
- Any error messages from your terminal.
