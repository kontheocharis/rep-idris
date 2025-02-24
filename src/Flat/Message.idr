module Flat.Message

import Flat.Lib
import Data.Fin
import Data.DPair

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

MkMessage : (source : Word) -> (dest : Word) -> (checksum : Word) -> {auto len : Word} -> BufOf len -> Message
MkMessage source dest checksum {len} payload = build
  (FieldData "source" source
  (FieldData "dest" dest
  (FieldData "checksum" checksum
  (ArrayData "payload" len payload))))
