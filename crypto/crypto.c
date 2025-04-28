// DES INSPIRED CRYPTO LIB 
//I AM NO CRYPTOGRAPHER, THIS HAS NO GUARENTEE TO BE CRYPTOGRAPHICALLY SECURE, DO NOT USE IN PRODUCTION IM JUST A DUMB COLLEGE KID WITH A TOUCH OF 'TISM
#include <ctype.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define BLOCK_SIZE 16
#define KEY_SIZE 32
#define ROUNDS 16
#define KDF_ITER 100000
#define SALT_SIZE 16
#define MAC_SIZE 4

static uint8_t sbox_table[256][256];
static uint8_t inv_sbox_table[256][256];

void init_sboxes() {
  for (int k = 0; k < 256; k++) {
    for (int x = 0; x < 256; x++) {
      uint8_t y = (((x << 3) & 0xFF) | (x >> 5)) ^ (uint8_t)k;
      y = (uint8_t)((y * 179 + 17) % 256);
      y = y ^ (y >> 4) ^ ((y << 3) & 0xFF);
      sbox_table[k][x] = y;
      inv_sbox_table[k][y] = (uint8_t)x;
    }
  }
}

static inline uint8_t custom_sbox(uint8_t x, uint8_t k) {
  return sbox_table[k][x];
}

static inline uint8_t inv_custom_sbox(uint8_t y, uint8_t k) {
  return inv_sbox_table[k][y];
}

void derive_rcon(const uint8_t salt[SALT_SIZE], const uint8_t key[KEY_SIZE],
                 uint8_t rcon[ROUNDS]) {
  uint8_t state = salt[0];
  for (int i = 0; i < ROUNDS; i++) {
    state = custom_sbox(state, key[i % KEY_SIZE]) ^ salt[i % SALT_SIZE];
    rcon[i] = state;
  }
}

void kdf_stretch(const uint8_t user_key[KEY_SIZE],
                 const uint8_t salt[SALT_SIZE], uint8_t out_key[KEY_SIZE]) {
  memcpy(out_key, user_key, KEY_SIZE);
  for (int iter = 0; iter < KDF_ITER; iter++) {
    for (int i = 0; i < KEY_SIZE; i++) {
      uint8_t v = out_key[i] ^ salt[i % SALT_SIZE];
      out_key[i] = custom_sbox(v, salt[(iter + i) % SALT_SIZE]);
    }
  }
}

void rotate_block(uint8_t b[BLOCK_SIZE], uint8_t s) {
  uint8_t t[BLOCK_SIZE];
  for (int i = 0; i < BLOCK_SIZE; i++)
    t[i] = b[(i + s) % BLOCK_SIZE];
  memcpy(b, t, BLOCK_SIZE);
}

static inline void inv_rotate_block(uint8_t b[BLOCK_SIZE], uint8_t s) {
  rotate_block(b, (BLOCK_SIZE - s) % BLOCK_SIZE);
}

void diffuse_block(uint8_t b[BLOCK_SIZE]) {
  for (int i = 1; i < BLOCK_SIZE; i++)
    b[i] ^= b[i - 1];
  for (int i = 0; i < BLOCK_SIZE; i++)
    b[i] = (uint8_t)((b[i] * 31 + 7) % 256);
}

void inv_diffuse_block(uint8_t b[BLOCK_SIZE]) {
  for (int i = 0; i < BLOCK_SIZE; i++)
    b[i] = (uint8_t)((b[i] - 7) * 223);
  for (int i = BLOCK_SIZE - 1; i >= 1; i--)
    b[i] ^= b[i - 1];
}

void expand_key(const uint8_t key[KEY_SIZE], const uint8_t rcon[ROUNDS],
                uint8_t rk[ROUNDS][BLOCK_SIZE]) {
  uint8_t tmp[BLOCK_SIZE];
  for (int i = 0; i < BLOCK_SIZE; i++)
    tmp[i] = key[i] ^ key[i + BLOCK_SIZE];
  for (int r = 0; r < ROUNDS; r++) {
    tmp[0] ^= rcon[r];
    for (int i = 0; i < BLOCK_SIZE; i++) {
      uint8_t kb = key[(r + i) % KEY_SIZE];
      uint8_t x = tmp[i] ^ key[(r * BLOCK_SIZE + i) % KEY_SIZE];
      rk[r][i] = custom_sbox(x, kb);
    }
    diffuse_block(tmp);
    for (int i = 0; i < BLOCK_SIZE; i++)
      tmp[i] ^= rk[r][i];
  }
}

void encrypt_round(uint8_t b[BLOCK_SIZE], const uint8_t rk[BLOCK_SIZE]) {
  for (int i = 0; i < BLOCK_SIZE; i++)
    b[i] = custom_sbox(b[i], rk[i]);
  diffuse_block(b);
  for (int i = 0; i < BLOCK_SIZE; i++)
    b[i] ^= rk[i];
}

void decrypt_round(uint8_t b[BLOCK_SIZE], const uint8_t rk[BLOCK_SIZE]) {
  for (int i = 0; i < BLOCK_SIZE; i++)
    b[i] ^= rk[i];
  inv_diffuse_block(b);
  for (int i = 0; i < BLOCK_SIZE; i++)
    b[i] = inv_custom_sbox(b[i], rk[i]);
}

size_t add_padding(uint8_t *d, size_t len) {
  uint8_t p = BLOCK_SIZE - (len % BLOCK_SIZE);
  if (p == 0)
    p = BLOCK_SIZE;
  memset(d + len, p, p);
  return len + p;
}

size_t remove_padding(const uint8_t *d, size_t len) {
  if (len == 0)
    return 0;
  uint8_t p = d[len - 1];
  if (p == 0 || p > BLOCK_SIZE)
    return 0;
  for (size_t i = len - p; i < len; i++)
    if (d[i] != p)
      return 0;
  return len - p;
}

int encrypt_and_auth(const uint8_t *in, size_t in_len,
                     const uint8_t k[KEY_SIZE], const uint8_t iv[BLOCK_SIZE],
                     const uint8_t salt[SALT_SIZE], uint8_t *out,
                     size_t *out_len) {
  uint8_t rcon[ROUNDS], key2[KEY_SIZE], rk[ROUNDS][BLOCK_SIZE];
  derive_rcon(salt, k, rcon);
  kdf_stretch(k, salt, key2);
  expand_key(key2, rcon, rk);

  uint8_t prev[BLOCK_SIZE], tmp[BLOCK_SIZE];
  memcpy(prev, iv, BLOCK_SIZE);

  size_t tot = ((in_len + BLOCK_SIZE) / BLOCK_SIZE) * BLOCK_SIZE;
  uint8_t *buf = calloc(1, tot);
  memcpy(buf, in, in_len);
  tot = add_padding(buf, in_len);

  for (size_t off = 0; off < tot; off += BLOCK_SIZE) {
    memcpy(tmp, buf + off, BLOCK_SIZE);
    for (int i = 0; i < BLOCK_SIZE; i++)
      tmp[i] ^= prev[i];
    for (int r = 0; r < ROUNDS; r++)
      encrypt_round(tmp, rk[r]);
    uint8_t s = prev[0] % BLOCK_SIZE;
    for (int i = 0; i < 6; i++)
      rotate_block(tmp, s);
    memcpy(out + off, tmp, BLOCK_SIZE);
    memcpy(prev, tmp, BLOCK_SIZE);
  }

  size_t c_len = tot;
  uint32_t mac = 0;
  for (size_t i = 0; i < c_len; i++)
    mac = (mac << 1) ^ out[i];
  memcpy(out + c_len, &mac, MAC_SIZE);
  *out_len = c_len + MAC_SIZE;

  free(buf);
  return 1;
}

int decrypt_and_verify(const uint8_t *in, size_t in_len,
                       const uint8_t k[KEY_SIZE], const uint8_t iv[BLOCK_SIZE],
                       const uint8_t salt[SALT_SIZE], uint8_t *out,
                       size_t *out_len) {
  if (in_len < MAC_SIZE)
    return 0;
  size_t c_len = in_len - MAC_SIZE;
  uint32_t mac_in;
  memcpy(&mac_in, in + c_len, MAC_SIZE);

  uint8_t key2[KEY_SIZE], rcon[ROUNDS], rk[ROUNDS][BLOCK_SIZE];
  kdf_stretch(k, salt, key2);
  derive_rcon(salt, k, rcon);
  expand_key(key2, rcon, rk);

  uint32_t mac_calc = 0;
  for (size_t i = 0; i < c_len; i++)
    mac_calc = (mac_calc << 1) ^ in[i];
  if (mac_calc != mac_in)
    return 0;

  uint8_t prev[BLOCK_SIZE], tmp[BLOCK_SIZE];
  memcpy(prev, iv, BLOCK_SIZE);

  for (size_t off = 0; off < c_len; off += BLOCK_SIZE) {
    memcpy(tmp, in + off, BLOCK_SIZE);
    uint8_t s = prev[0] % BLOCK_SIZE;
    for (int i = 0; i < 6; i++)
      inv_rotate_block(tmp, s);
    for (int r = ROUNDS - 1; r >= 0; r--)
      decrypt_round(tmp, rk[r]);
    for (int i = 0; i < BLOCK_SIZE; i++)
      out[off + i] = tmp[i] ^ prev[i];
    memcpy(prev, in + off, BLOCK_SIZE);
  }

  *out_len = remove_padding(out, c_len);
  return 1;
}

int main() {
  init_sboxes();
  srand((unsigned)time(NULL));

  uint8_t salt[SALT_SIZE], iv[BLOCK_SIZE], key[KEY_SIZE];
  for (int i = 0; i < SALT_SIZE; i++)
    salt[i] = rand() & 0xFF;
  for (int i = 0; i < BLOCK_SIZE; i++)
    iv[i] = rand() & 0xFF;
  memcpy(key, "key", KEY_SIZE);

  uint8_t key2[KEY_SIZE], rcon[ROUNDS], rk[ROUNDS][BLOCK_SIZE];
  kdf_stretch(key, salt, key2);
  derive_rcon(salt, key, rcon);
  expand_key(key2, rcon, rk);

  printf("Salt:           ");
  for (int i = 0; i < SALT_SIZE; i++)
    printf("%02x", salt[i]);
  printf("\n");
  printf("IV:             ");
  for (int i = 0; i < BLOCK_SIZE; i++)
    printf("%02x", iv[i]);
  printf("\n");
  printf("Key:            ");
  for (int i = 0; i < KEY_SIZE; i++)
    printf("%02x", key[i]);
  printf("\n");
  printf("Stretched Key:  ");
  for (int i = 0; i < KEY_SIZE; i++)
    printf("%02x", key2[i]);
  printf("\n");
  printf("RCON:           ");
  for (int i = 0; i < ROUNDS; i++)
    printf("%02x", rcon[i]);
  printf("\n");

  for (int r = 0; r < ROUNDS; r++) {
    printf("RK[%02d]:         ", r);
    for (int i = 0; i < BLOCK_SIZE; i++)
      printf("%02x", rk[r][i]);
    printf("\n");
  }

  const char *pt = "Hello World!";
  size_t pt_len = strlen(pt);
  size_t buf_len = ((pt_len + BLOCK_SIZE) / BLOCK_SIZE) * BLOCK_SIZE + MAC_SIZE;
  uint8_t *ct = malloc(buf_len), *rt = malloc(buf_len);
  size_t ct_len, rt_len;

  encrypt_and_auth((uint8_t *)pt, pt_len, key, iv, salt, ct, &ct_len);
  decrypt_and_verify(ct, ct_len, key, iv, salt, rt, &rt_len);

  printf("Original:       %s\n", pt);
  printf("Encrypted:      ");
  for (size_t i = 0; i < ct_len; i++)
    printf("%02x", ct[i]);
  printf("\n");
  printf("Decrypted:      ");
  for (size_t i = 0; i < rt_len; i++)
    putchar(rt[i]);
  printf("\n");

  free(ct);
  free(rt);
  return 0;
}
