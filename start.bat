@echo off
chcp 65001 >nul
title QingJian Quiz System
cd /d %~dp0
echo ==========================================
echo   QingJian Quiz System  http://127.0.0.1:8766/
echo   Close this window to stop the server
echo ==========================================
start "" http://127.0.0.1:8766/
py -3 server.py
if errorlevel 1 (
  echo.
  echo Server exited with an error. Try: py -3 server.py
  pause
)
