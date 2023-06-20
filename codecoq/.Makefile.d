theories/utiles.vo theories/utiles.glob theories/utiles.v.beautified theories/utiles.required_vo: theories/utiles.v 
theories/utiles.vio: theories/utiles.v 
theories/utiles.vos theories/utiles.vok theories/utiles.required_vos: theories/utiles.v 
theories/jeu.vo theories/jeu.glob theories/jeu.v.beautified theories/jeu.required_vo: theories/jeu.v theories/utiles.vo
theories/jeu.vio: theories/jeu.v theories/utiles.vio
theories/jeu.vos theories/jeu.vok theories/jeu.required_vos: theories/jeu.v theories/utiles.vos
theories/residu.vo theories/residu.glob theories/residu.v.beautified theories/residu.required_vo: theories/residu.v theories/utiles.vo theories/jeu.vo
theories/residu.vio: theories/residu.v theories/utiles.vio theories/jeu.vio
theories/residu.vos theories/residu.vok theories/residu.required_vos: theories/residu.v theories/utiles.vos theories/jeu.vos
theories/strategy.vo theories/strategy.glob theories/strategy.v.beautified theories/strategy.required_vo: theories/strategy.v theories/jeu.vo theories/residu.vo
theories/strategy.vio: theories/strategy.v theories/jeu.vio theories/residu.vio
theories/strategy.vos theories/strategy.vok theories/strategy.required_vos: theories/strategy.v theories/jeu.vos theories/residu.vos
theories/diagpol.vo theories/diagpol.glob theories/diagpol.v.beautified theories/diagpol.required_vo: theories/diagpol.v theories/jeu.vo theories/residu.vo theories/strategy.vo
theories/diagpol.vio: theories/diagpol.v theories/jeu.vio theories/residu.vio theories/strategy.vio
theories/diagpol.vos theories/diagpol.vok theories/diagpol.required_vos: theories/diagpol.v theories/jeu.vos theories/residu.vos theories/strategy.vos
theories/main.vo theories/main.glob theories/main.v.beautified theories/main.required_vo: theories/main.v theories/jeu.vo theories/residu.vo
theories/main.vio: theories/main.v theories/jeu.vio theories/residu.vio
theories/main.vos theories/main.vok theories/main.required_vos: theories/main.v theories/jeu.vos theories/residu.vos
tests/test.vo tests/test.glob tests/test.v.beautified tests/test.required_vo: tests/test.v theories/utiles.vo theories/main.vo theories/jeu.vo theories/residu.vo
tests/test.vio: tests/test.v theories/utiles.vio theories/main.vio theories/jeu.vio theories/residu.vio
tests/test.vos tests/test.vok tests/test.required_vos: tests/test.v theories/utiles.vos theories/main.vos theories/jeu.vos theories/residu.vos
