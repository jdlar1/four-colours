# Prueba de prioridad

Cada snapshot tiene:
- `manifest-<fecha>.sha256`: hash SHA-256 de cada archivo de `four-colours/` (incluidos los grandes que no están en git).
- `anchor-<fecha>.txt`: fecha, commit de git y hash del manifiesto.
- `*.ots`: sellos OpenTimestamps (anclados en Bitcoin). A los calendarios solo se envió el hash, no el contenido.

## Completar el sello (unas horas después)
    cd priority && ots upgrade *.ots

## Verificar
    ots verify manifest-<fecha>.sha256.ots     # prueba la fecha
    cd .. && sha256sum -c priority/manifest-<fecha>.sha256   # prueba que los archivos no cambiaron

Guarda copia de esta carpeta y de los archivos grandes fuera de este PC: si se pierden, el hash no basta para reconstruirlos.
