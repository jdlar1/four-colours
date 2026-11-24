# Limit native workers even when a Python search starts several processes.
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 NUMEXPR_NUM_THREADS=1
export PYTHONDONTWRITEBYTECODE=1
export OMP_THREAD_LIMIT=1 HIGHS_THREADS=1
