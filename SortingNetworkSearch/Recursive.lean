import SortingNetworkSearch.Base

class Recursive t [Base t] [f : Functor (Base.base t)] where
  project : t → Base.base t t
