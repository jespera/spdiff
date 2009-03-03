void sem_exit_ns(struct ipc_namespace *ns)
{
	free_ipcs(ns, &sem_ids(ns), freeary);
}


static inline void sem_rmid(struct ipc_namespace *ns, struct sem_array *s)
{
	ipc_rmid(&sem_ids(ns), &s->sem_perm);
}


asmlinkage long SyS_semctl(int semid, int semnum, int cmd, union semun arg)
{
	return SYSC_semctl((int) semid, (int) semnum, (int) cmd, arg);
}


static inline struct mqueue_inode_info *MQUEUE_I(struct inode *inode)
{
	return container_of(inode, struct mqueue_inode_info, vfs_inode);
}

static struct inode *mqueue_get_inode(struct super_block *sb, int mode,
			 int flags, const char *dev_name,
			 void *data, struct vfsmount *mnt)
{
	return get_sb_single(fs_type, flags, data, mqueue_fill_super, mnt);
}



static void mqueue_destroy_inode(struct inode *inode)
{
	kmem_cache_free(mqueue_inode_cachep, MQUEUE_I(inode));
}



static inline void set_cookie(struct sk_buff *skb, char code)
{
	((char*)skb->data)[NOTIFY_COOKIE_LEN-1] = code;
}



static void ipc_memory_notifier(struct work_struct *work)
{
	ipcns_notify(IPCNS_MEMCHANGED);
}



void ipc_rcu_getref(void *ptr)
{
	container_of(ptr, struct ipc_rcu_hdr, data)->refcount++;
}

static void ipc_do_vfree(struct work_struct *work)
{
	vfree(container_of(work, struct ipc_rcu_sched, work));
}


int ipcget(struct ipc_namespace *ns, struct ipc_ids *ids,
			struct ipc_ops *ops, struct ipc_params *params)
{
	if (params->key == IPC_PRIVATE)
		return ipcget_new(ns, ids, ops, params);
	else
		return ipcget_public(ns, ids, ops, params);
}


void shm_exit_ns(struct ipc_namespace *ns)
{
	free_ipcs(ns, &shm_ids(ns), do_shm_rmid);
}


static inline void shm_rmid(struct ipc_namespace *ns, struct shmid_kernel *s)
{
	ipc_rmid(&shm_ids(ns), &s->shm_perm);
}



int ipcns_notify(unsigned long val)
{
	return blocking_notifier_call_chain(&ipcns_chain, val, NULL);
}
void msg_exit_ns(struct ipc_namespace *ns)
{
	free_ipcs(ns, &msg_ids(ns), freeque);
}


static inline void msg_rmid(struct ipc_namespace *ns, struct msg_queue *s)
{
	ipc_rmid(&msg_ids(ns), &s->q_perm);
}



static void crypto_proc_fips_init(void)
{
	crypto_sysctls = register_sysctl_table(crypto_dir_table);
}



static void *c_next(struct seq_file *m, void *p, loff_t *pos)
{
	return seq_list_next(p, &crypto_alg_list, pos);
}

static void c_stop(struct seq_file *m, void *p)
{
	up_read(&crypto_alg_sem);
}



static int crypto_info_open(struct inode *inode, struct file *file)
{
	return seq_open(file, &crypto_seq_ops);
}
        

static inline u64 Ch(u64 x, u64 y, u64 z)
{
        return z ^ (x & (y ^ z));
}

static inline u64 Maj(u64 x, u64 y, u64 z)
{
        return (x & y) | (z & (x | y));
}

static inline u64 RORu64(u64 x, u64 y)
{
        return (x >> y) | (x << (64 - y));
}


static inline void LOAD_OP(int I, u64 *W, const u8 *input)
{
	W[I] = __be64_to_cpu( ((__be64*)(input))[I] );
}

static inline void BLEND_OP(int I, u64 *W)
{
	W[I] = s1(W[I-2]) + W[I-7] + s0(W[I-15]) + W[I-16];
}


static void __exit async_xor_exit(void)
{
	do { } while (0);
}


static int __init async_memset_init(void)
{
	return 0;
}

static void __exit async_memset_exit(void)
{
	do { } while (0);
}


static void __exit async_tx_exit(void)
{
	dmaengine_put();
}



static void __exit async_tx_exit(void)
{
	do { } while (0);
}


static int __init async_memcpy_init(void)
{
	return 0;
}

static void __exit async_memcpy_exit(void)
{
	do { } while (0);
}


static int __init rmd320_mod_init(void)
{
	return crypto_register_shash(&alg);
}

static void __exit rmd320_mod_fini(void)
{
	crypto_unregister_shash(&alg);
}


static inline u32 F(u32 x, u32 y, u32 z)
{
	return (x & y) | ((~x) & z);
}

static inline u32 G(u32 x, u32 y, u32 z)
{
	return (x & y) | (x & z) | (y & z);
}

static inline u32 H(u32 x, u32 y, u32 z)
{
	return x ^ y ^ z;
}


static int __init md4_mod_init(void)
{
	return crypto_register_shash(&alg);
}

static void __exit md4_mod_fini(void)
{
	crypto_unregister_shash(&alg);
}


void *scatterwalk_map(struct scatter_walk *walk, int out)
{
	return crypto_kmap(scatterwalk_page(walk), out) +
	       offset_in_page(walk->offset);
}


static void __exit khazad_mod_fini(void)
{
	crypto_unregister_alg(&khazad_alg);
}



static int cryptd_blkcipher_encrypt_enqueue(struct ablkcipher_request *req)
{
	return cryptd_blkcipher_enqueue(req, cryptd_blkcipher_encrypt);
}

static int cryptd_blkcipher_decrypt_enqueue(struct ablkcipher_request *req)
{
	return cryptd_blkcipher_enqueue(req, cryptd_blkcipher_decrypt);
}



static int cryptd_hash_init_enqueue(struct ahash_request *req)
{
	return cryptd_hash_enqueue(req, cryptd_hash_init);
}



static int cryptd_hash_update_enqueue(struct ahash_request *req)
{
	return cryptd_hash_enqueue(req, cryptd_hash_update);
}



static int cryptd_hash_final_enqueue(struct ahash_request *req)
{
	return cryptd_hash_enqueue(req, cryptd_hash_final);
}



static int cryptd_hash_digest_enqueue(struct ahash_request *req)
{
	return cryptd_hash_enqueue(req, cryptd_hash_digest);
}



void cryptd_free_ablkcipher(struct cryptd_ablkcipher *tfm)
{
	crypto_free_ablkcipher(&tfm->base);
}


static inline struct crypto_shash *__crypto_shash_cast(struct crypto_tfm *tfm)
{
	return container_of(tfm, struct crypto_shash, base);
}

static inline unsigned int shash_align_buffer_size(unsigned len,
						   unsigned long mask)
{
	return len + (mask & ~(__alignof__(u8 __attribute__ ((aligned))) - 1));
}


static int shash_finup_unaligned(struct shash_desc *desc, const u8 *data,
				 unsigned int len, u8 *out)
{
	return crypto_shash_update(desc, data, len) ?:
	       crypto_shash_final(desc, out);
}


static int shash_digest_unaligned(struct shash_desc *desc, const u8 *data,
				  unsigned int len, u8 *out)
{
	return crypto_shash_init(desc) ?:
	       crypto_shash_update(desc, data, len) ?:
	       crypto_shash_final(desc, out);
}



static int shash_async_final(struct ahash_request *req)
{
	return crypto_shash_final(ahash_request_ctx(req), req->result);
}



static int shash_compat_final(struct hash_desc *hdesc, u8 *out)
{
	return crypto_shash_final(crypto_hash_ctx(hdesc->tfm), out);
}


static int crypto_shash_init_tfm(struct crypto_tfm *tfm,
				 const struct crypto_type *frontend)
{
	return 0;
}

static unsigned int crypto_shash_extsize(struct crypto_alg *alg,
					 const struct crypto_type *frontend)
{
	return alg->cra_ctxsize;
}


struct crypto_shash *crypto_alloc_shash(const char *alg_name, u32 type,
					u32 mask)
{
	return __crypto_shash_cast(
		crypto_alloc_tfm(alg_name, &crypto_shash_type, type, mask));
}


int crypto_unregister_shash(struct shash_alg *alg)
{
	return crypto_unregister_alg(&alg->base);
}

static unsigned int crypto_hash_ctxsize(struct crypto_alg *alg, u32 type,
					u32 mask)
{
	return alg->cra_ctxsize;
}



static int __init camellia_init(void)
{
	return crypto_register_alg(&camellia_alg);
}

static void __exit camellia_fini(void)
{
	crypto_unregister_alg(&camellia_alg);
}

static unsigned int crypto_ablkcipher_ctxsize(struct crypto_alg *alg, u32 type,
					      u32 mask)
{
	return alg->cra_ctxsize;
}

int skcipher_null_givencrypt(struct skcipher_givcrypt_request *req)
{
	return crypto_ablkcipher_encrypt(&req->creq);
}

int skcipher_null_givdecrypt(struct skcipher_givcrypt_request *req)
{
	return crypto_ablkcipher_decrypt(&req->creq);
}



static int no_givdecrypt(struct skcipher_givcrypt_request *req)
{
	return -ENOSYS;
}



const char *crypto_default_geniv(const struct crypto_alg *alg)
{
	return alg->cra_flags & CRYPTO_ALG_ASYNC ? "eseqiv" : "chainiv";
}



static int __init deflate_mod_init(void)
{
	return crypto_register_alg(&alg);
}

static void __exit deflate_mod_fini(void)
{
	crypto_unregister_alg(&alg);
}


static int __init rmd128_mod_init(void)
{
	return crypto_register_shash(&alg);
}

static void __exit rmd128_mod_fini(void)
{
	crypto_unregister_shash(&alg);
}


static inline int tcrypt_test(const char *alg)
{
	return alg_test(alg, alg, 0, 0);
}

static void do_test(int m)

{
	return crypto_register_template(&seqiv_tmpl);
}

static void __exit seqiv_module_exit(void)
{
	crypto_unregister_template(&seqiv_tmpl);
}


struct crypto_template *crypto_lookup_template(const char *name)
{
	return try_then_request_module(__crypto_lookup_template(name), name);
}


int crypto_register_notifier(struct notifier_block *nb)
{
	return blocking_notifier_chain_register(&crypto_chain, nb);
}

int crypto_unregister_notifier(struct notifier_block *nb)
{
	return blocking_notifier_chain_unregister(&crypto_chain, nb);
}


static void __exit crypto_algapi_exit(void)
{
	crypto_exit_proc();
}


static int __init cast5_mod_init(void)
{
	return crypto_register_alg(&alg);
}

static void __exit cast5_mod_fini(void)
{
	crypto_unregister_alg(&alg);
}


static inline void *align_ptr(void *p, unsigned int align)
{
	return (void *)ALIGN((unsigned long)p, align);
}

static inline struct hmac_ctx *hmac_ctx(struct crypto_hash *tfm)
{
	return align_ptr(crypto_hash_ctx_aligned(tfm) +
			 crypto_hash_blocksize(tfm) * 2 +
			 crypto_hash_digestsize(tfm), sizeof(void *));
}


static void __exit hmac_module_exit(void)
{
	crypto_unregister_template(&hmac_tmpl);
}


static void __exit crypto_cts_module_exit(void)
{
	crypto_unregister_template(&crypto_cts_tmpl);
}


static inline void blkcipher_map_src(struct blkcipher_walk *walk)
{
	walk->src.virt.addr = scatterwalk_map(&walk->in, 0);
}

static inline void blkcipher_map_dst(struct blkcipher_walk *walk)
{
	walk->dst.virt.addr = scatterwalk_map(&walk->out, 1);
}

static inline void blkcipher_unmap_src(struct blkcipher_walk *walk)
{
	scatterwalk_unmap(walk->src.virt.addr, 0);
}

static inline void blkcipher_unmap_dst(struct blkcipher_walk *walk)
{
	scatterwalk_unmap(walk->dst.virt.addr, 1);
}


static int async_setkey(struct crypto_ablkcipher *tfm, const u8 *key,
			unsigned int keylen)
{
	return setkey(crypto_ablkcipher_tfm(tfm), key, keylen);
}



void skcipher_geniv_exit(struct crypto_tfm *tfm)
{
	crypto_free_ablkcipher(tfm->crt_ablkcipher.base);
}

static unsigned int crypto_rng_ctxsize(struct crypto_alg *alg, u32 type,
				       u32 mask)
{
	return alg->cra_ctxsize;
}


static void chainiv_module_exit(void)
{
	crypto_unregister_template(&chainiv_tmpl);
}


static int __init md5_mod_init(void)
{
	return crypto_register_shash(&alg);
}

static void __exit md5_mod_fini(void)
{
	crypto_unregister_shash(&alg);
}

static inline u8
byte(const u32 x, const unsigned n)
{
	return x >> (n << 3);
}



static int __init seed_init(void)
{
	return crypto_register_alg(&seed_alg);
}

static void __exit seed_fini(void)
{
	crypto_unregister_alg(&seed_alg);
}


static void __exit eseqiv_module_exit(void)
{
	crypto_unregister_template(&eseqiv_tmpl);
}

static void __exit crypto_module_exit(void)
{
	crypto_unregister_template(&crypto_tmpl);
}


static void __exit anubis_mod_fini(void)
{
	crypto_unregister_alg(&anubis_alg);
}


static void __exit crypto_cbc_module_exit(void)
{
	crypto_unregister_template(&crypto_cbc_tmpl);
}


static int __init fcrypt_mod_init(void)
{
	return crypto_register_alg(&fcrypt_alg);
}

static void __exit fcrypt_mod_fini(void)
{
	crypto_unregister_alg(&fcrypt_alg);
}


static int __init blowfish_mod_init(void)
{
	return crypto_register_alg(&alg);
}

static void __exit blowfish_mod_fini(void)
{
	crypto_unregister_alg(&alg);
}


static void free_prng_context(struct prng_context *ctx)
{
	crypto_free_cipher(ctx->tfm);
}



static void cprng_exit(struct crypto_tfm *tfm)
{
	free_prng_context(crypto_tfm_ctx(tfm));
}



static inline void setbit128_bbe(void *b, int bit)
{
	__set_bit(bit ^ 0x78, b);
}



static void __exit crypto_module_exit(void)
{
	crypto_unregister_template(&crypto_tmpl);
}

static int ahash_nosetkey(struct crypto_ahash *tfm, const u8 *key,
			  unsigned int keylen)
{
	return -ENOSYS;
}


static unsigned int crypto_ahash_ctxsize(struct crypto_alg *alg, u32 type,
					u32 mask)
{
	return alg->cra_ctxsize;
}



static void hexdump(unsigned char *buf, unsigned int len)
{
	print_hex_dump(KERN_CONT, "", DUMP_PREFIX_OFFSET,
			16, 1,
			buf, len, false);
}



static int __init rmd256_mod_init(void)
{
	return crypto_register_shash(&alg);
}

static void __exit rmd256_mod_fini(void)
{
	crypto_unregister_shash(&alg);
}


static int __init arc4_init(void)
{
	return crypto_register_alg(&arc4_alg);
}


static void __exit arc4_exit(void)
{
	crypto_unregister_alg(&arc4_alg);
}


static inline u32 xswap(u32 val)
{
	return ((val & 0x00ff00ff) << 8) | ((val & 0xff00ff00) >> 8);
}



static int __init michael_mic_init(void)
{
	return crypto_register_shash(&alg);
}


static void __exit michael_mic_exit(void)
{
	crypto_unregister_shash(&alg);
}



static inline u32 Ch(u32 x, u32 y, u32 z)
{
	return z ^ (x & (y ^ z));
}

static inline u32 Maj(u32 x, u32 y, u32 z)
{
	return (x & y) | (z & (x | y));
}


static inline void LOAD_OP(int I, u32 *W, const u8 *input)
{
	W[I] = __be32_to_cpu( ((__be32*)(input))[I] );
}

static inline void BLEND_OP(int I, u32 *W)
{
	W[I] = s1(W[I-2]) + W[I-7] + s0(W[I-15]) + W[I-16];
}

static void sha256_transform(u32 *state, const u8 *input)

{
	return crypto_register_template(&crypto_pcbc_tmpl);
}

static void __exit crypto_pcbc_module_exit(void)
{
	crypto_unregister_template(&crypto_pcbc_tmpl);
}


struct crypto_alg *crypto_mod_get(struct crypto_alg *alg)
{
	return try_module_get(alg->cra_module) ? crypto_alg_get(alg) : NULL;
}


static inline int crypto_is_test_larval(struct crypto_larval *larval)
{
	return larval->alg.cra_driver_name[0];
}

static struct crypto_alg *__crypto_alg_lookup(const char *name, u32 type,
                            const u8 *src, unsigned int slen,
                            u8 *dst, unsigned int *dlen)
{
	return tfm->__crt_alg->cra_compress.coa_compress(tfm, src, slen, dst,
	                                                 dlen);
}

static int crypto_decompress(struct crypto_tfm *tfm,
                             const u8 *src, unsigned int slen,
                             u8 *dst, unsigned int *dlen)
{
	return tfm->__crt_alg->cra_compress.coa_decompress(tfm, src, slen, dst,
	                                                   dlen);
}



static int __init rmd160_mod_init(void)
{
	return crypto_register_shash(&alg);
}

static void __exit rmd160_mod_fini(void)
{
	crypto_unregister_shash(&alg);
}


static int null_init(struct shash_desc *desc)
{
	return 0;
}

static int null_update(struct shash_desc *desc, const u8 *data,
		       unsigned int len)
{
	return 0;
}

static int null_final(struct shash_desc *desc, u8 *out)
{
	return 0;
}

static int null_digest(struct shash_desc *desc, const u8 *data,
		       unsigned int len, u8 *out)
{
	return 0;
}

static int null_hash_setkey(struct crypto_shash *tfm, const u8 *key,
			    unsigned int keylen)
{ return 0; }

static int null_setkey(struct crypto_tfm *tfm, const u8 *key,
		       unsigned int keylen)
{ return 0; }

static void null_crypt(struct crypto_tfm *tfm, u8 *dst, const u8 *src)
{
	memcpy(dst, src, NULL_BLOCK_SIZE);
}



static int __init sha1_generic_mod_init(void)
{
	return crypto_register_shash(&alg);
}

static void __exit sha1_generic_mod_fini(void)
{
	crypto_unregister_shash(&alg);
}


static int __init salsa20_generic_mod_init(void)
{
	return crypto_register_alg(&alg);
}

static void __exit salsa20_generic_mod_fini(void)
{
	crypto_unregister_alg(&alg);
}



static void __exit crypto_xcbc_module_exit(void)
{
	crypto_unregister_template(&crypto_xcbc_tmpl);
}


static inline u8 byte(const u32 x, const unsigned n)
{
	return x >> (n << 3);
}



static int __init aes_init(void)
{
	return crypto_register_alg(&aes_alg);
}

static void __exit aes_fini(void)
{
	crypto_unregister_alg(&aes_alg);
}


static void __exit crypto_authenc_module_exit(void)
{
	crypto_unregister_template(&crypto_authenc_tmpl);
}


static int __init lzo_mod_init(void)
{
	return crypto_register_alg(&alg);
}

static void __exit lzo_mod_fini(void)
{
	crypto_unregister_alg(&alg);
}


static int __init crc32c_mod_init(void)
{
	return crypto_register_shash(&alg);
}

static void __exit crc32c_mod_fini(void)
{
	crypto_unregister_shash(&alg);
}

static unsigned int crypto_aead_ctxsize(struct crypto_alg *alg, u32 type,
					u32 mask)
{
	return alg->cra_ctxsize;
}

static int no_givcrypt(struct aead_givcrypt_request *req)
{
	return -ENOSYS;
}



static int aead_null_givencrypt(struct aead_givcrypt_request *req)
{
	return crypto_aead_encrypt(&req->areq);
}

static int aead_null_givdecrypt(struct aead_givcrypt_request *req)
{
	return crypto_aead_decrypt(&req->areq);
}



void aead_geniv_exit(struct crypto_tfm *tfm)
{
	crypto_free_aead(tfm->crt_aead.base);
}


static int __init cast6_mod_init(void)
{
	return crypto_register_alg(&alg);
}

static void __exit cast6_mod_fini(void)
{
	crypto_unregister_alg(&alg);
}


static void __exit crypto_ecb_module_exit(void)
{
	crypto_unregister_template(&crypto_ecb_tmpl);
}


static int __init twofish_mod_init(void)
{
	return crypto_register_alg(&alg);
}

static void __exit twofish_mod_fini(void)
{
	crypto_unregister_alg(&alg);
}


static int krng_reset(struct crypto_rng *tfm, u8 *seed, unsigned int slen)
{
	return 0;
}



static int __init krng_mod_init(void)
{
	return crypto_register_alg(&krng_alg);
}



static void blk_add_trace_rq_abort(struct request_queue *q, struct request *rq)
{
	blk_add_trace_rq(q, rq, BLK_TA_ABORT);
}

static void blk_add_trace_rq_insert(struct request_queue *q, struct request *rq)
{
	blk_add_trace_rq(q, rq, BLK_TA_INSERT);
}

static void blk_add_trace_rq_issue(struct request_queue *q, struct request *rq)
{
	blk_add_trace_rq(q, rq, BLK_TA_ISSUE);
}

static void blk_add_trace_rq_requeue(struct request_queue *q,
				     struct request *rq)
{
	blk_add_trace_rq(q, rq, BLK_TA_REQUEUE);
}

static void blk_add_trace_rq_complete(struct request_queue *q,
				      struct request *rq)
{
	blk_add_trace_rq(q, rq, BLK_TA_COMPLETE);
}



static void blk_add_trace_bio_bounce(struct request_queue *q, struct bio *bio)
{
	blk_add_trace_bio(q, bio, BLK_TA_BOUNCE);
}

static void blk_add_trace_bio_complete(struct request_queue *q, struct bio *bio)
{
	blk_add_trace_bio(q, bio, BLK_TA_COMPLETE);
}

static void blk_add_trace_bio_backmerge(struct request_queue *q,
					struct bio *bio)
{
	blk_add_trace_bio(q, bio, BLK_TA_BACKMERGE);
}

static void blk_add_trace_bio_frontmerge(struct request_queue *q,
					 struct bio *bio)
{
	blk_add_trace_bio(q, bio, BLK_TA_FRONTMERGE);
}

static void blk_add_trace_bio_queue(struct request_queue *q, struct bio *bio)
{
	blk_add_trace_bio(q, bio, BLK_TA_QUEUE);
}


static inline
const struct blk_io_trace *te_blk_io_trace(const struct trace_entry *ent)
{
	return (const struct blk_io_trace *)ent;
}

static inline const void *pdu_start(const struct trace_entry *ent)
{
	return te_blk_io_trace(ent) + 1;
}

static inline u32 t_sec(const struct trace_entry *ent)
{
	return te_blk_io_trace(ent)->bytes >> 9;
}

static inline unsigned long long t_sector(const struct trace_entry *ent)
{
	return te_blk_io_trace(ent)->sector;
}

static inline __u16 t_error(const struct trace_entry *ent)
{
	return te_blk_io_trace(ent)->sector;
}



static int blk_log_plug(struct trace_seq *s, const struct trace_entry *ent)
{
	return trace_seq_printf(s, "[%s]\n", trace_find_cmdline(ent->pid));
}

static int blk_log_unplug(struct trace_seq *s, const struct trace_entry *ent)
{
	return trace_seq_printf(s, "[%s] %llu\n", trace_find_cmdline(ent->pid),
				get_pdu_int(ent));
}

static int blk_log_split(struct trace_seq *s, const struct trace_entry *ent)
{
	return trace_seq_printf(s, "%llu / %llu [%s]\n", t_sector(ent),
				get_pdu_int(ent), trace_find_cmdline(ent->pid));
}


static enum print_line_t
blk_trace_event_print_binary(struct trace_iterator *iter, int flags)
{
	return blk_trace_synthesize_old_trace(iter) ?
			TRACE_TYPE_HANDLED : TRACE_TYPE_PARTIAL_LINE;
}



static int compat_put_ushort(unsigned long arg, unsigned short val)
{
	return put_user(val, (unsigned short __user *)compat_ptr(arg));
}

static int compat_put_int(unsigned long arg, int val)
{
	return put_user(val, (compat_int_t __user *)compat_ptr(arg));
}

static int compat_put_long(unsigned long arg, long val)
{
	return put_user(val, (compat_long_t __user *)compat_ptr(arg));
}

static int compat_put_ulong(unsigned long arg, compat_ulong_t val)
{
	return put_user(val, (compat_ulong_t __user *)compat_ptr(arg));
}

static int compat_put_u64(unsigned long arg, u64 val)
{
	return put_user(val, (compat_u64 __user *)compat_ptr(arg));
}


static inline struct rb_root *
deadline_rb_root(struct deadline_data *dd, struct request *rq)
{
	return &dd->sort_list[rq_data_dir(rq)];
}


static ssize_t
deadline_var_show(int var, char *page)
{
	return sprintf(page, "%d\n", var);
}



static void __exit deadline_exit(void)
{
	elv_unregister(&iosched_deadline);
}


static int scsi_get_idlun(struct request_queue *q, int __user *p)
{
	return put_user(0, p);
}

static int scsi_get_bus(struct request_queue *q, int __user *p)
{
	return put_user(0, p);
}

static int sg_get_timeout(struct request_queue *q)
{
	return jiffies_to_clock_t(q->sg_timeout);
}


 
static int sg_emulated_host(struct request_queue *q, int __user *p)
{
	return put_user(1, p);
}


static inline int blk_send_start_stop(struct request_queue *q,
				      struct gendisk *bd_disk, int data)
{
	return __blk_send_generic(q, bd_disk, GPCMD_START_STOP_UNIT, data);
}


static ssize_t
queue_var_show(unsigned int var, char *page)
{
	return sprintf(page, "%d\n", var);
}



static ssize_t queue_requests_show(struct request_queue *q, char *page)
{
	return queue_var_show(q->nr_requests, (page));
}



static ssize_t queue_hw_sector_size_show(struct request_queue *q, char *page)
{
	return queue_var_show(q->hardsect_size, page);
}



static ssize_t queue_nonrot_show(struct request_queue *q, char *page)
{
	return queue_var_show(!blk_queue_nonrot(q), page);
}



static ssize_t queue_nomerges_show(struct request_queue *q, char *page)
{
	return queue_var_show(blk_queue_nomerges(q), page);
}



static ssize_t queue_iostats_show(struct request_queue *q, char *page)
{
	return queue_var_show(blk_queue_io_stat(q), page);
}


 
void blk_queue_prep_rq(struct request_queue *q, prep_rq_fn *pfn)
{
	q->prep_rq_fn = pfn;
}

 
void blk_queue_set_discard(struct request_queue *q, prepare_discard_fn *dfn)
{
	q->prepare_discard_fn = dfn;
}

 
void blk_queue_merge_bvec(struct request_queue *q, merge_bvec_fn *mbfn)
{
	q->merge_bvec_fn = mbfn;
}

void blk_queue_softirq_done(struct request_queue *q, softirq_done_fn *fn)
{
	q->softirq_done_fn = fn;
}

void blk_queue_rq_timeout(struct request_queue *q, unsigned int timeout)
{
	q->rq_timeout = timeout;
}

void blk_queue_rq_timed_out(struct request_queue *q, rq_timed_out_fn *fn)
{
	q->rq_timed_out_fn = fn;
}

void blk_queue_lld_busy(struct request_queue *q, lld_busy_fn *fn)
{
	q->lld_busy_fn = fn;
}


void blk_queue_hardsect_size(struct request_queue *q, unsigned short size)
{
	q->hardsect_size = size;
}


void blk_queue_dma_pad(struct request_queue *q, unsigned int mask)
{
	q->dma_pad_mask = mask;
}


void blk_queue_dma_alignment(struct request_queue *q, int mask)
{
	q->dma_alignment = mask;
}


static int __init setup_fail_io_timeout(char *str)
{
	return setup_fault_attr(&fail_io_timeout, str);
}



static int __init fail_io_timeout_debugfs(void)
{
	return init_fault_attr_dentries(&fail_io_timeout, "fail_io_timeout");
}


 
void blk_delete_timer(struct request *req)
{
	list_del_init(&req->timeout_list);
}



static inline void as_del_rq_rb(struct as_data *ad, struct request *rq)
{
	elv_rb_del(RQ_RB_ROOT(ad, rq), rq);
}


static ssize_t
as_var_show(unsigned int var, char *page)
{
	return sprintf(page, "%d\n", var);
}



struct request *blk_queue_find_tag(struct request_queue *q, int tag)
{
	return blk_map_queue_find_tag(q->queue_tags, tag);
}


void blk_queue_free_tags(struct request_queue *q)
{
	queue_flag_clear_unlocked(QUEUE_FLAG_QUEUED, q);
}


struct blk_queue_tag *blk_init_tags(int depth)
{
	return __blk_queue_init_tags(NULL, depth);
}


void blk_put_queue(struct request_queue *q)
{
	kobject_put(&q->kobj);
}



struct request_queue *blk_alloc_queue(gfp_t gfp_mask)
{
	return blk_alloc_queue_node(gfp_mask, -1);
}


struct request_queue *blk_init_queue(request_fn_proc *rfn, spinlock_t *lock)
{
	return blk_init_queue_node(rfn, lock, -1);
}


static int __init setup_fail_make_request(char *str)
{
	return setup_fault_attr(&fail_make_request, str);
}


static int __init fail_make_request_debugfs(void)
{
	return init_fault_attr_dentries(&fail_make_request,
					"fail_make_request");
}

late_initcall(fail_make_request_debugfs);

static inline int should_fail_request(struct bio *bio)
{
	return 0;
}


int blk_end_request(struct request *rq, int error, unsigned int nr_bytes)
{
	return blk_end_io(rq, error, nr_bytes, 0, NULL);
}

int blk_end_bidi_request(struct request *rq, int error, unsigned int nr_bytes,
			 unsigned int bidi_bytes)
{
	return blk_end_io(rq, error, nr_bytes, bidi_bytes, NULL);
}


int kblockd_schedule_work(struct request_queue *q, struct work_struct *work)
{
	return queue_work(kblockd_workqueue, work);
}


static inline int sector_in_part(struct hd_struct *part, sector_t sector)
{
	return part->start_sect <= sector &&
		sector < part->start_sect + part->nr_sects;
}



static inline int major_to_index(int major)
{
	return major % BLKDEV_MAJOR_HASH_SIZE;
}


void blk_unregister_region(dev_t devt, unsigned long range)
{
	kobj_unmap(bdev_map, devt, range);
}


static int partitions_open(struct inode *inode, struct file *file)
{
	return seq_open(file, &partitions_op);
}


static int diskstats_open(struct inode *inode, struct file *file)
{
	return seq_open(file, &diskstats_op);
}


struct gendisk *alloc_disk(int minors)
{
	return alloc_disk_node(minors, -1);
}


void set_device_ro(struct block_device *bdev, int flag)
{
	bdev->bd_part->policy = flag;
}

static int raise_blk_irq(int cpu, struct request *rq)
{
	return 1;
}


static int put_ushort(unsigned long arg, unsigned short val)
{
	return put_user(val, (unsigned short __user *)arg);
}

static int put_int(unsigned long arg, int val)
{
	return put_user(val, (int __user *)arg);
}

static int put_long(unsigned long arg, long val)
{
	return put_user(val, (long __user *)arg);
}

static int put_ulong(unsigned long arg, unsigned long val)
{
	return put_user(val, (unsigned long __user *)arg);
}

static int put_u64(unsigned long arg, u64 val)
{
	return put_user(val, (u64 __user *)arg);
}


static inline struct cfq_queue *cic_to_cfqq(struct cfq_io_context *cic,
					    int is_sync)
{
	return cic->cfqq[!!is_sync];
}

static inline void cic_set_cfqq(struct cfq_io_context *cic,
				struct cfq_queue *cfqq, int is_sync)
{
	cic->cfqq[!!is_sync] = cfqq;
}


static inline int
cfq_prio_to_slice(struct cfq_data *cfqd, struct cfq_queue *cfqq)
{
	return cfq_prio_slice(cfqd, cfq_cfqq_sync(cfqq), cfqq->ioprio);
}


static inline sector_t cfq_dist_from_last(struct cfq_data *cfqd,
					  struct request *rq)
{
	if (rq->sector >= cfqd->last_position)
		return rq->sector - cfqd->last_position;
	else
		return cfqd->last_position - rq->sector;
}



static void cfq_cic_free(struct cfq_io_context *cic)
{
	call_rcu(&cic->rcu_head, cfq_cic_free_rcu);
}

 
static void cfq_exit_io_context(struct io_context *ioc)
{
	call_for_each_cic(ioc, cfq_exit_single_io_context);
}


static ssize_t
cfq_var_show(unsigned int var, char *page)
{
	return sprintf(page, "%d\n", var);
}


static void noop_merged_requests(struct request_queue *q, struct request *rq,
				 struct request *next)
{
	list_del_init(&next->queuelist);
}


static void __exit noop_exit(void)
{
	elv_unregister(&elevator_noop);
}


static inline struct hlist_head *bsg_dev_idx_hash(int index)
{
	return &bsg_device_list[index & (BSG_LIST_ARRAY_SIZE - 1)];
}



static void elevator_put(struct elevator_type *e)
{
	module_put(e->elevator_owner);
}


static void *elevator_init_queue(struct request_queue *q,
				 struct elevator_queue *eq)
{
	return eq->ops->elevator_init_fn(q);
}



static inline void __elv_rqhash_del(struct request *rq)
{
	hlist_del_init(&rq->hash);
}



static ssize_t integrity_format_show(struct blk_integrity *bi, char *page)
{
	if (bi != NULL && bi->name != NULL)
		return sprintf(page, "%s\n", bi->name);
	else
		return sprintf(page, "none\n");
}

static ssize_t integrity_tag_size_show(struct blk_integrity *bi, char *page)
{
	if (bi != NULL)
		return sprintf(page, "%u\n", bi->tag_size);
	else
		return sprintf(page, "0\n");
}



static ssize_t integrity_read_show(struct blk_integrity *bi, char *page)
{
	return sprintf(page, "%d\n", (bi->flags & INTEGRITY_FLAG_READ) != 0);
}



static ssize_t integrity_write_show(struct blk_integrity *bi, char *page)
{
	return sprintf(page, "%d\n", (bi->flags & INTEGRITY_FLAG_WRITE) != 0);
}



static int set_if_up(char *ifname, short flags)
{
	return set_if_flags(ifname, flags | IFF_UP);
}

static int set_if_down(char *ifname, short flags)
{
	return set_if_flags(ifname, flags & ~IFF_UP);
}



void print_delayacct(struct taskstats *t)
{
	printf("\n\nCPU   %15s%15s%15s%15s\n"
	       "      %15llu%15llu%15llu%15llu\n"
	       "IO    %15s%15s\n"
	       "      %15llu%15llu\n"
	       "SWAP  %15s%15s\n"
	       "      %15llu%15llu\n"
	       "RECLAIM  %12s%15s\n"
	       "      %15llu%15llu\n",
	       "count", "real total", "virtual total", "delay total",
	       (unsigned long long)t->cpu_count,
	       (unsigned long long)t->cpu_run_real_total,
	       (unsigned long long)t->cpu_run_virtual_total,
	       (unsigned long long)t->cpu_delay_total,
	       "count", "delay total",
	       (unsigned long long)t->blkio_count,
	       (unsigned long long)t->blkio_delay_total,
	       "count", "delay total",
	       (unsigned long long)t->swapin_count,
	       (unsigned long long)t->swapin_delay_total,
	       "count", "delay total",
	       (unsigned long long)t->freepages_count,
	       (unsigned long long)t->freepages_delay_total);
}

void task_context_switch_counts(struct taskstats *t)
{
	printf("\n\nTask   %15s%15s\n"
	       "       %15llu%15llu\n",
	       "voluntary", "nonvoluntary",
	       (unsigned long long)t->nvcsw, (unsigned long long)t->nivcsw);
}

void print_cgroupstats(struct cgroupstats *c)
{
	printf("sleeping %llu, blocked %llu, running %llu, stopped %llu, "
		"uninterruptible %llu\n", (unsigned long long)c->nr_sleeping,
		(unsigned long long)c->nr_io_wait,
		(unsigned long long)c->nr_running,
		(unsigned long long)c->nr_stopped,
		(unsigned long long)c->nr_uninterruptible);
}


void print_ioacct(struct taskstats *t)
{
	printf("%s: read=%llu, write=%llu, cancelled_write=%llu\n",
		t->ac_comm,
		(unsigned long long)t->read_bytes,
		(unsigned long long)t->write_bytes,
		(unsigned long long)t->cancelled_write_bytes);
}



static inline struct childless *to_childless(struct config_item *item)
{
	return item ? container_of(to_configfs_subsystem(to_config_group(item)), struct childless, subsys) : NULL;
}


static ssize_t childless_storeme_read(struct childless *childless,
				      char *page)
{
	return sprintf(page, "%d\n", childless->storeme);
}


static ssize_t childless_description_read(struct childless *childless,
					  char *page)
{
	return sprintf(page,
"[01-childless]\n"
"\n"
"The childless subsystem is the simplest possible subsystem in\n"
"configfs.  It does not support the creation of child config_items.\n"
"than a directory in /proc.\n");
}



static inline struct simple_child *to_simple_child(struct config_item *item)
{
	return item ? container_of(item, struct simple_child, item) : NULL;
}



static void simple_child_release(struct config_item *item)
{
	kfree(to_simple_child(item));
}



static inline struct simple_children *to_simple_children(struct config_item *item)
{
	return item ? container_of(to_config_group(item), struct simple_children, group) : NULL;
}



static void simple_children_release(struct config_item *item)
{
	kfree(to_simple_children(item));
}


static inline struct childless *to_childless(struct config_item *item)
{
	return item ? container_of(to_configfs_subsystem(to_config_group(item)), struct childless, subsys) : NULL;
}


static ssize_t childless_storeme_read(struct childless *childless,
				      char *page)
{
	return sprintf(page, "%d\n", childless->storeme);
}


static ssize_t childless_description_read(struct childless *childless,
					  char *page)
{
	return sprintf(page,
"[01-childless]\n"
"\n"
"The childless subsystem is the simplest possible subsystem in\n"
"configfs.  It does not support the creation of child config_items.\n"
"than a directory in /proc.\n");
}



static inline struct simple_child *to_simple_child(struct config_item *item)
{
	return item ? container_of(item, struct simple_child, item) : NULL;
}



static void simple_child_release(struct config_item *item)
{
	kfree(to_simple_child(item));
}



static inline struct simple_children *to_simple_children(struct config_item *item)
{
	return item ? container_of(to_config_group(item), struct simple_children, group) : NULL;
}



static void simple_children_release(struct config_item *item)
{
	kfree(to_simple_children(item));
}

 
void cfag12864b_blit(void)
{
	memcpy(cfag12864b_mem, cfag12864b_buffer, CFAG12864B_SIZE);
}


static int snd_aicapcm_pcm_hw_params(struct snd_pcm_substream
				     *hw_params)
{

	return
	    snd_pcm_lib_malloc_pages(substream,
				     params_buffer_bytes(hw_params));
}


static unsigned long snd_aicapcm_pcm_pointer(struct snd_pcm_substream
					     *substream)
{
	return readl(AICA_CONTROL_CHANNEL_SAMPLE_NUMBER);
}


static int snd_amd7930_hw_params(struct snd_pcm_substream *substream,
				    struct snd_pcm_hw_params *hw_params)
{
	return snd_pcm_lib_malloc_pages(substream, params_buffer_bytes(hw_params));
}

static int snd_amd7930_hw_free(struct snd_pcm_substream *substream)
{
	return snd_pcm_lib_free_pages(substream);
}



static int __init amd7930_init(void)
{
	return of_register_driver(&amd7930_sbus_driver, &of_bus_type);
}



static int snd_cs4231_xrate(struct snd_pcm_runtime *runtime)
{
	return snd_pcm_hw_constraint_list(runtime, 0,
					  SNDRV_PCM_HW_PARAM_RATE,
					  &hw_constraints_rates);
}



static u8 __cs4231_readb(struct snd_cs4231 *cp, void __iomem *reg_addr)
{
	if (cp->flags & CS4231_FLAG_EBUS)
		return readb(reg_addr);
	else
		return sbus_readb(reg_addr);
}

static void __cs4231_writeb(struct snd_cs4231 *cp, u8 val,
			    void __iomem *reg_addr)
{
	if (cp->flags & CS4231_FLAG_EBUS)
		return writeb(val, reg_addr);
	else
		return sbus_writeb(val, reg_addr);
}


static int _ebus_dma_request(struct cs4231_dma_control *dma_cont,
			     dma_addr_t bus_addr, size_t len)
{
	return ebus_dma_request(&dma_cont->ebus_info, bus_addr, len);
}

static void _ebus_dma_enable(struct cs4231_dma_control *dma_cont, int on)
{
	ebus_dma_enable(&dma_cont->ebus_info, on);
}

static void _ebus_dma_prepare(struct cs4231_dma_control *dma_cont, int dir)
{
	ebus_dma_prepare(&dma_cont->ebus_info, dir);
}

static unsigned int _ebus_dma_addr(struct cs4231_dma_control *dma_cont)
{
	return ebus_dma_addr(&dma_cont->ebus_info);
}



static int __init cs4231_init(void)
{
	return of_register_driver(&cs4231_driver, &of_bus_type);
}

static void __exit cs4231_exit(void)
{
	of_unregister_driver(&cs4231_driver);
}


static inline int pipe_active(struct snd_dbri *dbri, int pipe)
{
	return ((pipe >= 0) && (dbri->pipes[pipe].desc != -1));
}



static int __init dbri_init(void)
{
	return of_register_driver(&dbri_sbus_driver, &of_bus_type);
}

static void __exit dbri_exit(void)
{
	of_unregister_driver(&dbri_sbus_driver);
}

static int davinci_pcm_hw_params(struct snd_pcm_substream *substream,
				 struct snd_pcm_hw_params *hw_params)
{
	return snd_pcm_lib_malloc_pages(substream,
					params_buffer_bytes(hw_params));
}

static int davinci_pcm_hw_free(struct snd_pcm_substream *substream)
{
	return snd_pcm_lib_free_pages(substream);
}



static int __init davinci_soc_platform_init(void)
{
	return snd_soc_register_platform(&davinci_soc_platform);
}

static void __exit davinci_soc_platform_exit(void)
{
	snd_soc_unregister_platform(&davinci_soc_platform);
}

static inline void davinci_mcbsp_write_reg(struct davinci_mcbsp_dev *dev,
					   int reg, u32 val)
{
	__raw_writel(val, dev->base + reg);
}

static inline u32 davinci_mcbsp_read_reg(struct davinci_mcbsp_dev *dev, int reg)
{
	return __raw_readl(dev->base + reg);
}



static int __init davinci_i2s_init(void)
{
	return snd_soc_register_dai(&davinci_i2s_dai);
}

static void __exit davinci_i2s_exit(void)
{
	snd_soc_unregister_dai(&davinci_i2s_dai);
}

