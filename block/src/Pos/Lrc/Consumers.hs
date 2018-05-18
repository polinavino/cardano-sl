{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE RankNTypes          #-}

module Pos.Lrc.Consumers
       (
         allLrcConsumers
       ) where

import           Pos.Delegation.Lrc (dlgLrcConsumer)
import           Pos.Lrc.Consumer (LrcConsumer)
import           Pos.Lrc.Mode (LrcMode)
import           Pos.Ssc.Lrc (sscLrcConsumer)
import           Pos.Update.Lrc (usLrcConsumer)
import           Pos.Core (HasGenesisBlockVersionData)

allLrcConsumers
    :: forall ctx m. (LrcMode ctx m, HasGenesisBlockVersionData)
    => [LrcConsumer m]
allLrcConsumers = [dlgLrcConsumer, usLrcConsumer, sscLrcConsumer]
