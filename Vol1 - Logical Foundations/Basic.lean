inductive Day where
  | monday
  | tuesday
  | wednedsay
  | thursday
  | friday
  | saturday
  | sunday
  deriving
    Repr,
    DecidableEq

def nextWorkingDay (d : Day) : Day :=
  match d with
  | Day.monday    => Day.tuesday
  | Day.tuesday   => Day.wednedsay
  | Day.wednedsay => Day.thursday
  | Day.thursday  => Day.friday
  | Day.friday    => Day.monday
  | Day.saturday  => Day.monday
  | Day.sunday    => Day.monday
