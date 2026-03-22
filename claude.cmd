set PATH=%PATH%C:\Program Files\Git\cmd;C:\Program Files\GitHub CLI;%USERPROFILE%\.local\bin;%USERPROFILE%\.elan\bin
gh auth login --git-protocol https --with-token < claude_git_auth_token.txt
pause
claude --continue
