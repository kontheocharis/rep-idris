module Flat.Message

import Flat.Lib

messageProtocol : Protocol 4 Infinite
messageProtocol = WithField "source" (WithField "dest" (WithField "checksum" (WithArray "payload")))

0 Message : Type
Message = BufFor messageProtocol

(.source) : Message -> Word
(.source) m = getField "source" m

(.dest) : Message -> Word
(.dest) m = getField "dest" m

(.checksum) : Message -> Word
(.checksum) m = getField "checksum" m

(.payloadLength) : Message -> Word
(.payloadLength) m = getField "payload" m

(.payload) : (m : Message) -> BufOf m.payloadLength
(.payload) m = getArray "payload" m
