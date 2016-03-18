/*
 * Copyright (c) 2014-2016, Yue Du
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without modification,
 * are permitted provided that the following conditions are met:
 *
 *     * Redistributions of source code must retain the above copyright notice,
 *       this list of conditions and the following disclaimer.
 *     * Redistributions in binary form must reproduce the above copyright notice,
 *       this list of conditions and the following disclaimer in the documentation
 *       and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
 * WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
 * CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
 * OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 */


#include <Python.h>
#include <stdint.h>
#include <ctype.h>
#include <stdio.h>

#define TOSTRING(x) #x
#define VALUE_TO_STRING(x) TOSTRING(x)

#ifndef Py_TYPE
#define Py_TYPE(ob) (((PyObject*)(ob))->ob_type)
#endif

#if PY_MAJOR_VERSION >= 3
#define PyString_FromStringAndSize PyBytes_FromStringAndSize
#define PyString_AS_STRING PyBytes_AsString
#endif

#define XFREE(o) do { if ((o) == NULL) ; else free(o); } while (0)

#define DELTA 0x9e3779b9
#define MX (((z>>5^y<<2) + (y>>3^z<<4)) ^ ((sum^y) + (key[(p&3)^e] ^ z)))

static PyObject *module, *binascii;
static PyObject *_xxtea_pyunicode_hexlify;
static PyObject *_xxtea_pyunicode_unhexlify;
static PyObject *_xxtea_pyunicode_decrypt;


int ti_xxtea_encrypt(const unsigned char* str, int slen, const unsigned char* key, int keylen, unsigned char* enc_chr, int enclen) 
{
    unsigned int* v = NULL;
    int vlen;

    int n;
    int q;

    unsigned int z;
    unsigned int y;
    unsigned int delta;
    unsigned int mx, e;
    unsigned int sum;
    int i;
    unsigned int k[4];

    vlen = (slen & 3);
    if(vlen == 0){
        vlen = slen + 4;
    }
    else{
        vlen = slen + 8 - vlen;
    }

    if(enc_chr == NULL){
        return vlen;
    }
    if(enclen < vlen) return -1;

    enclen = vlen;

    if(enc_chr != str){
        memcpy(enc_chr, str, slen * sizeof(unsigned char));
    }


    v = (unsigned int*)enc_chr;
    vlen = enclen >> 2;

    v[vlen - 1] = slen;

    if((slen & 3) != 0){
        memset((enc_chr + slen), 0, (4 - (slen & 3)) * sizeof(unsigned char));
    }

    memcpy(k, key, keylen);

    n = vlen - 1;
    z = v[n];
    y = v[0];
    delta = 0x9E3779B9;
    q = 6 + 52 / (n + 1);
    sum = 0;
    while (0 < q--) {
        sum = sum + delta ;
        e = sum >> 2 & 3;
        for (i = 0; i < n; i++) {
            y = v[i + 1];
            mx = (unsigned int)(z >> 5 ^ y << 2) + (unsigned int)(y >> 3 ^ z << 4) ^ (sum ^ y) + (unsigned int)(k[((unsigned int)i) & 3 ^ e] ^ z);
            z = v[i] = v[i] + mx ;
        }
        y = v[0];
        mx = (z >> 5 ^ y << 2) + (y >> 3 ^ z << 4) ^ (sum ^ y) + (k[((unsigned int)i) & 3 ^ e] ^ z);
        z = v[n] = v[n] + mx & 0xffffffff;
    }

    return vlen << 2;
}

int ti_xxtea_decrypt(const unsigned char* str, int slen, const unsigned char* key, int keylen, unsigned char* dec_chr, int declen) {
    unsigned int* v = NULL;
    int vlen;
    int i;

    int n;
    unsigned int z;
    unsigned int y;
    unsigned int delta;
    unsigned int mx, e;
    int q;
    unsigned int sum;
    unsigned int k[4];

    vlen = slen;
    if((slen & 3) != 0){
        return -1;
    }

    if(dec_chr == NULL){
        return vlen;
    }
    if(declen < vlen) return -2;

    declen = vlen;

    if(dec_chr != str){
        memcpy(dec_chr, str, slen * sizeof(unsigned char));
    }

    v = (unsigned int*)dec_chr;
    vlen = declen >> 2;

    memcpy(k, key, keylen);  

    n = vlen - 1;
    if (n == 0) {
        return -3;
    }
    z = v[n - 1];
    y = v[0];
    delta = 0x9E3779B9;
    q = 6 + 52 / (n + 1);
    sum = q * delta;

    while (sum != 0) {
        e = sum >> 2 & 3;
        for (i = n; i > 0; i--) {
            z = v[i - 1];
            mx = (unsigned int)(z >> 5 ^ y << 2) + (unsigned int)(y >> 3 ^ z << 4) ^ (sum ^ y) + (unsigned int)(k[((unsigned int)i) & 3 ^ e] ^ z);
            y = v[i] = v[i] - mx;
        }
        z = v[n];
        mx = (z >> 5 ^ y << 2) + (y >> 3 ^ z << 4) ^ (sum ^ y) + (k[((unsigned int)i) & 3 ^ e] ^ z);
        y = v[0] = v[0] - mx;
        sum = sum - delta;
    }

    n = v[vlen - 1];
    
    if(n >= 0 && n <= (vlen - 1) * 4){
        dec_chr[n] = '\0';
        return n;
    }
    return -4;
}


/*****************************************************************************
 * Module Functions ***********************************************************
 ****************************************************************************/

static char *keywords[] = {"data", "key", NULL};


PyDoc_STRVAR(
    xxtea_encrypt_doc,
    "encrypt (data, key)\n\n"
    "Encrypt `data` with a 16-byte `key`, return binary bytes.");

static PyObject *xxtea_encrypt(PyObject *self, PyObject *args, PyObject *kwargs)
{
    const char *data, *key;
    int alen, dlen, klen;
    PyObject *retval;
    char *retbuf;
    uint32_t *d, k[4];

    d = NULL;
    retval = NULL;
    k[0] = k[1] = k[2] = k[3] = 0;

    if (!PyArg_ParseTupleAndKeywords(args, kwargs, "s#s#", keywords, &data, &dlen, &key, &klen)) {
        return NULL;
    }

    if (klen != 16) {
        PyErr_SetString(PyExc_ValueError, "Need a 16-byte key.");
        return NULL;
    }

    alen = dlen < 4 ? 2 : (dlen >> 2) + 1 + 2;
    d = (uint32_t *)calloc(alen, sizeof(uint32_t));

    if (d == NULL) {
        return PyErr_NoMemory();
    }

    // bytes2longs(data, dlen, d, 1);
    // bytes2longs(key, klen, k, 0);
    // btea(d, alen, k);

    // retval = PyString_FromStringAndSize(NULL, (alen << 2));

    // if (!retval) {
    //     goto cleanup;
    // }

    // retbuf = PyString_AS_STRING(retval);
    // longs2bytes(d, alen, retbuf, 0);

    int outlen = ti_xxtea_encrypt(data, dlen, key, klen, (uint8_t*)d, alen << 2);
    retval = PyString_FromStringAndSize(NULL, outlen);
    if (!retval) {
        goto cleanup;
    }
    retbuf = PyString_AS_STRING(retval);
    memcpy(retbuf, d, outlen);
    free(d);

    return retval;

cleanup:
    XFREE(d);
    Py_XDECREF(retval);
    return NULL;
}

PyDoc_STRVAR(
    xxtea_encrypt_hex_doc,
    "encrypt_hex (data, key)\n\n"
    "Encrypt `data` with a 16-byte `key`, return hex encoded bytes.");

static PyObject *xxtea_encrypt_hex(PyObject *self, PyObject *args, PyObject *kwargs)
{
    PyObject *retval, *tmp;
    retval = tmp = NULL;

    if (!(tmp = xxtea_encrypt(self, args, kwargs))) {
        return NULL;
    }

    retval = PyObject_CallMethodObjArgs(binascii, _xxtea_pyunicode_hexlify, tmp, NULL);
    Py_DECREF(tmp);

    return retval;
}

PyDoc_STRVAR(
    xxtea_decrypt_doc,
    "decrypt (data, key)\n\n"
    "Decrypt `data` with a 16-byte `key`, return original bytes.");

static PyObject *xxtea_decrypt(PyObject *self, PyObject *args, PyObject *kwargs)
{
    const char *data, *key;
    int alen, dlen, klen, rc;
    PyObject *retval;
    char *retbuf;
    uint32_t *d, k[4];

    d = NULL;
    retval = NULL;
    k[0] = k[1] = k[2] = k[3] = 0;

    if (!PyArg_ParseTupleAndKeywords(args, kwargs, "s#s#", keywords, &data, &dlen, &key, &klen)) {
        return NULL;
    }

    if (klen != 16) {
        PyErr_SetString(PyExc_ValueError, "Need a 16-byte key.");
        return NULL;
    }

    /* not divided by 4, or length < 8 */
    if (dlen & 3 || dlen < 8) {
        PyErr_SetString(PyExc_ValueError, "Invalid data, data length is not a multiple of 4, or less than 8.");
        goto cleanup;
    }

    alen = dlen / 4 + 1;
    d = (uint32_t *)calloc(alen, sizeof(uint32_t));

    if (d == NULL) {
        PyErr_NoMemory();
        goto cleanup;

    }

    // bytes2longs(data, dlen, d, 0);
    // bytes2longs(key, klen, k, 0);
    // btea(d, -alen, k);

    // rc = longs2bytes(d, alen, retbuf, 1);
    // if (rc >= 0) {
    //     /* Remove PKCS#7 padded chars */
    //     Py_SIZE(retval) = rc;
    // }
    // else {
    //     /* Illegal PKCS#7 padding */
    //     PyErr_SetString(PyExc_ValueError, "Invalid data, illegal PKCS#7 padding. Could be using a wrong key.");
    //     goto cleanup;
    // }

    int outlen = ti_xxtea_decrypt(data, dlen, key, klen, (uint8_t*)d, alen << 2);
    retval = PyString_FromStringAndSize(NULL, outlen);
    if (!retval) {
        return NULL;
    }
    retbuf = PyString_AS_STRING(retval);

    memcpy(retbuf, d, outlen);
    free(d);

    return retval;

cleanup:
    XFREE(d);
    Py_XDECREF(retval);
    return NULL;
}

PyDoc_STRVAR(
    xxtea_decrypt_hex_doc,
    "decrypt_hex (data, key)\n\n"
    "Decrypt hex encoded `data` with a 16-byte `key`, return original bytes.");

static PyObject *xxtea_decrypt_hex(PyObject *self, PyObject *args, PyObject *kwargs)
{
    PyObject *data, *key, *retval, *tmp;
    data = key = retval = tmp = NULL;

    if (!PyArg_ParseTupleAndKeywords(args, kwargs, "SS", keywords, &data, &key)) {
        return NULL;
    }

    if (!(tmp = PyObject_CallMethodObjArgs(binascii, _xxtea_pyunicode_unhexlify, data, NULL))) {
        return NULL;
    }

    retval = PyObject_CallMethodObjArgs(module, _xxtea_pyunicode_decrypt, tmp, key, NULL);
    Py_DECREF(tmp);

    return retval;
}

/*****************************************************************************
 * Module Init ****************************************************************
 ****************************************************************************/

/* ref: https://docs.python.org/2/howto/cporting.html */



static PyMethodDef methods[] = {
    {"encrypt", (PyCFunction)xxtea_encrypt, METH_VARARGS | METH_KEYWORDS, xxtea_encrypt_doc},
    {"decrypt", (PyCFunction)xxtea_decrypt, METH_VARARGS | METH_KEYWORDS, xxtea_decrypt_doc},
    {"encrypt_hex", (PyCFunction)xxtea_encrypt_hex, METH_VARARGS | METH_KEYWORDS, xxtea_encrypt_hex_doc},
    {"decrypt_hex", (PyCFunction)xxtea_decrypt_hex, METH_VARARGS | METH_KEYWORDS, xxtea_decrypt_hex_doc},
    {NULL, NULL, 0, NULL}
};

#if PY_MAJOR_VERSION >= 3

static struct PyModuleDef moduledef = {
    PyModuleDef_HEAD_INIT,
    "xxtea",
    NULL,
    -1,
    methods,
    NULL,
    NULL,
    NULL,
    NULL
};

#define INITERROR return NULL

PyObject *PyInit_xxtea(void)

#else

#define INITERROR return

void initxxtea(void)
#endif
{
#if PY_MAJOR_VERSION >= 3
    module = PyModule_Create(&moduledef);
#else
    module = Py_InitModule("xxtea", methods);
#endif

    if (module == NULL) {
        INITERROR;
    }
    if (!(binascii = PyImport_ImportModule("binascii"))) {
        Py_DECREF(module);
        INITERROR;
    }

    _xxtea_pyunicode_hexlify = PyUnicode_FromString("hexlify");
    _xxtea_pyunicode_unhexlify = PyUnicode_FromString("unhexlify");
    _xxtea_pyunicode_decrypt = PyUnicode_FromString("decrypt");

    PyModule_AddStringConstant(module, "VERSION", VALUE_TO_STRING(VERSION));

#if PY_MAJOR_VERSION >= 3
    return module;
#endif
}
