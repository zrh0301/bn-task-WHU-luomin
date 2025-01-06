#include "../inc/wlc_bn.h"

#ifdef ENABLE_BN_MEM
void bn_set_zero(dig_t *x, int digs){
	for (int i = 0; i < digs; ++i){
		x[i] = 0;
	}
}

void bn_rand(dig_t *x, int digs){
	for (int i = 0; i < digs; i++){
		x[i] = rand();
	}
}

void bn_copy(dig_t *r, const dig_t *x, int digs){
	for (int i = 0; i < digs; ++i) r[i] = x[i];
}

int bn_get_bits(const dig_t *x, int digs){
	int bits = digs << 5;
	for (int i = digs - 1; i >= 0; --i){
		if (x[i] == 0) bits -= 32;
		else{
			register dig_t cur = x[i];
			for (int j = 0; j < 32; ++j){
				cur >>= 1;
				if (cur == 0){
					bits -= (31 - j);
					return bits;
				}
			}
		}
		return 0;
	}
}
#endif

#ifdef ENABLE_BN_ADD
dig_t bn_add(dig_t *r, const dig_t *x, const dig_t *y, int digs){
	int i = 0;
	register udi_t carry = 0;
	for (i = 0; i < digs; ++i){
		carry += (udi_t)x[i] + (udi_t)y[i];
		r[i] = (dig_t)carry;
		carry >>= 32;
	}
	return (dig_t)carry;
}

dig_t bn_sub(dig_t *r, const dig_t *x, const dig_t *y, int digs){
	register dig_t carry = 0;
	for (int i = 0; i < digs; ++i){
		sdi_t tpx = (sdi_t)x[i];
		sdi_t tpy = (sdi_t)y[i];
		r[i] = x[i] - y[i] - carry;
		carry = ((tpx - carry) < tpy);
	}
	return carry;
}

void bn_mul(dig_t* r,const dig_t* x,const dig_t* y,int digs){
    bn_set_zero(r,digs<<1);
    for(int i=0;i<digs;++i){
        for(int j=0;j<digs;++j){
            register udi_t tmp=(udi_t)x[i]*(udi_t)y[j];
            dig_t tmp_high=tmp>>32;
            dig_t tmp_low=(dig_t)tmp;
            r[i+j+1]+=bn_add(r+i+j,r+i+j,&tmp_low,1);
            r[i+j+2]+=bn_add(r+i+j+1,r+i+j+1,&tmp_high,1);
        }
    }
}

#endif

#ifdef ENABLE_BN_CMP
int bn_cmp(const dig_t *x, const dig_t *y, int digs){
	for (int i = digs - 1; i >= 0; --i){
		if (x[i] < y[i]) return -1;
		else if (x[i] > y[i]) return 1;
	}
	return 0;
}
#endif

#ifdef ENABLE_BN_SHIFT
dig_t bn_lsh_low(dig_t *r, const dig_t *x, int bits, int digs){
	if (bits >= 32){
		while (bits >= 31){
			bn_lsh_low(x, x, 31, digs);
			bits -= 31;
		}
		return bn_lsh_low(x, x, bits, digs);
	}

	dig_t carry, carry_new = 0;

	for (int i = 0; i < digs; ++i){
		carry = carry_new;
		carry_new = x[i] >> (32 - bits);
		r[i] = (x[i] << bits) + carry;
	}
	return carry_new;
}

dig_t bn_rsh_low(dig_t *r, const dig_t *x, int bits, int digs){
	if (bits >= 32){
		while (bits >= 31){
			bn_rsh_low(x, x, 31, digs);
			bits -= 31;
		}
		return bn_rsh_low(x, x, bits, digs);
	}

	dig_t carry, carry_new = 0;

	for (int i = digs - 1; i >= 0; --i){
		carry = carry_new;
		carry_new = (*(x + i)) << 32 - bits;
		r[i] = (x[i] >> bits) + carry;
	}
	return carry_new >> (32 - bits);
}
#endif

#ifdef ENABLE_BN_MOD
void bn_mod_add(dig_t *r, const dig_t *x, const dig_t *y, const dig_t *m, int digs){
	register dig_t *temp = calloc((digs + 1), sizeof(dig_t));
	register dig_t *m_new = calloc((digs + 1), sizeof(dig_t));
	bn_copy(m_new, m, digs);

	temp[digs] = bn_add(temp, x, y, digs);
	while (bn_cmp(temp, m_new, digs + 1) >= 0) bn_sub(temp, temp, m_new, digs + 1);

	bn_copy(r, temp, digs);
	free(temp);
	free(m_new);
}

void bn_mod_sub(dig_t *r, const dig_t *x, const dig_t *y, const dig_t *m, int digs){
	register dig_t *temp = calloc((digs + 1), sizeof(dig_t));
	register dig_t *m_new = calloc((digs + 1), sizeof(dig_t));
	bn_copy(m_new, m, digs);

	temp[digs] = bn_sub(temp, x, y, digs);
	while (bn_cmp(temp, m_new, digs + 1) >= 0) bn_sub(temp, temp, m_new, digs + 1);

	bn_copy(r, temp, digs);
	free(temp);
	free(m_new);
}

void bn_mod_hlv(dig_t *r, const dig_t *x, const dig_t *m, int digs){
	if(x[0] & 1 == 1) bn_add(r, x, m, digs);
	bn_rsh_low(r, x, 1, digs);
	while(bn_cmp(r, m, digs) >= 0) bn_sub(r, r, m, digs);
}

void bn_mod_rdc(dig_t *r, const dig_t *x, const dig_t *m, int xdigs, int mdigs)
{
	dig_t *carry = calloc(mdigs + 1, sizeof(dig_t));
	dig_t *m_new = calloc(mdigs + 1, sizeof(dig_t));
	dig_t *carry_now = calloc(mdigs + 1, sizeof(dig_t));
	dig_t *r_new = calloc(mdigs + 1, sizeof(dig_t));
	dig_t *temp = calloc(mdigs + 1, sizeof(dig_t));
	dig_t *x_new = calloc(xdigs / mdigs * mdigs + ((xdigs % mdigs == 0) ? 0 : 1) * mdigs, sizeof(dig_t));
	bn_copy(m_new, m, mdigs);
	bn_copy(x_new, x, xdigs);

	carry[mdigs] = 1;
	carry_now[0] = 1;

	for (int i = 0; i < xdigs; i += mdigs){
		bn_mod_mul(temp, x_new + i, carry_now, m, mdigs);
		bn_add(r_new, temp, r_new, mdigs + 1);

		while (bn_cmp(r_new, m_new, mdigs + 1) >= 0) bn_sub(r_new, r_new, m_new, mdigs + 1);
		bn_mod_mul(carry_now, carry_now, carry, m_new, mdigs + 1);
	}

	bn_copy(r, r_new, mdigs);
	free(carry);
	free(m_new);
	free(carry_now);
	free(r_new);
	free(temp);
	free(x_new);
}

void bn_mod_mul(dig_t *r, const dig_t *x, const dig_t *y, const dig_t *m, int digs){
	int digs_new = digs + 1;
	dig_t *zero_bn = calloc(digs, sizeof(dig_t));
	dig_t *x_new = calloc(digs_new, sizeof(dig_t));
	dig_t *r_new = calloc(digs_new, sizeof(dig_t));
	dig_t *y_new = calloc(digs, sizeof(dig_t));
	dig_t *m_new = calloc(digs_new, sizeof(dig_t));
	bn_copy(x_new, x, digs);
	bn_copy(y_new, y, digs);
	bn_copy(m_new, m, digs);

	while (bn_cmp(x_new, m_new, digs) >= 0) bn_sub(x_new, x_new, m_new, digs);
	while (bn_cmp(y_new, m_new, digs) >= 0) bn_sub(y_new, y_new, m_new, digs);

	while (bn_cmp(y_new, zero_bn, digs)){
		if (y_new[0] & 1 == 1){
			bn_add(r_new, r_new, x_new, digs + 1);
			while (bn_cmp(r_new, m_new, digs + 1) >= 0) bn_sub(r_new, r_new, m_new, digs + 1);
		}

		bn_lsh_low(x_new, x_new, 1, digs_new);
		while (bn_cmp(x_new, m_new, digs_new) > 0) bn_sub(x_new, x_new, m_new, digs_new);
		bn_rsh_low(y_new, y_new, 1, digs);
	}

	bn_copy(r, r_new, digs);
	free(x_new);
	free(y_new);
	free(m_new);
	free(r_new);
	free(zero_bn);
}

void bn_mod_exp(dig_t *r, const dig_t *x, const dig_t *e, const dig_t *m, int digs){
	dig_t *x_new = calloc(digs, sizeof(dig_t));
	dig_t *e_new = calloc(digs, sizeof(dig_t));
	dig_t *zero_bn = calloc(digs, sizeof(dig_t));
	bn_copy(x_new, x, digs);
	bn_copy(e_new, e, digs);

	bn_set_zero(r, digs);
	r[0] = 1;

	while (bn_cmp(x_new, m, digs) >= 0) bn_sub(x_new, x_new, m, digs);

	register dig_t carry = 0;
	for (int count = 0; count < digs << 5; ++count){
		carry = bn_lsh_low(e_new, e_new, 1, digs);
		bn_mod_mul(r, r, r, m, digs);
		if (carry) bn_mod_mul(r, r, x_new, m, digs);
	}

	free(x_new);
	free(e_new);
	free(zero_bn);
}
#endif