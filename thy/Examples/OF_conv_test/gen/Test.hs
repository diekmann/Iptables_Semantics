import Prelude
import O
import Data.Time

ofi2 sfw =
  fun_app (map (serialize_of_entry (the . map_of sQRL_ports)) . theRight)
      (lr_of_tran sQRL_rtbl_main_sorted sfw sQRL_ifs);

main = do
	n <- readLn
	t1 <- getCurrentTime
	sfw <- return $! Prelude.take n sQRL_fw_simple
	t2 <- getCurrentTime
	_ <- print $ Prelude.length (ofi2 sfw)
	t3 <- getCurrentTime
	_ <- putStrLn (show (diffUTCTime t2 t1) ++ " " ++ show (diffUTCTime t3 t2))
	return ()
