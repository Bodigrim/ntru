ntru-haskell
============

A Haskell Implementation of the NTRU Cryptographic library, following the IEEE Standard Specification (IEEE Std 1363.1-2008).
Developed by Theo Levine, Elizabeth Hughes, and Tom Cornelius at Cyberpoint LLC (www.cyberpointllc.com).  Special thanks as well to Paul Li and Ian Blumenfeld.

You can build it by running:
```
cabal install NTRU
```

or by downloading it and then running: 
```
cabal configure
cabal build
cabal install 
```
You can ignore the warnings from the build. 

A prebuilt hackage is available at http://hackage.haskell.org/package/NTRU. You may need to install some dependencies, such as llvm. 

Please contact opensource@cyberpointllc.com with any questions. 

Copyright 2013 CyberPoint International LLC.

This program is free software; you can redistribute it and/or
modify it under the terms of the GNU General Public License
as published by the Free Software Foundation; either version 2
of the License, or (at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program; if not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301, USA.
